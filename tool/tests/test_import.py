"""Tests of `hpf import`: the findings of another reviewer go into the ladder. No test makes a model call."""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, Dict

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))
if str(TOOL / "tests") not in sys.path:
    sys.path.insert(0, str(TOOL / "tests"))

from hpflow import briefs, outside  # noqa: E402
from hpflow.common import UsageError  # noqa: E402
from test_hpflow import FakeRunner, FlowCase  # noqa: E402

SHOWN = "def run():\n    from pkg.mod import add\n    return repr(add(2, 3))\n"


class ImportRunner(FakeRunner):
    """A worker of `import`: it shows the claims whose text has "real", and gives a reason for each other claim.
    A claim with "silent" in its text gets no answer."""

    def run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        if not (folder / "outside_claims.json").exists():
            return super().run(graph, folder)
        shown, not_shown = [], []
        for c in json.loads((folder / "outside_claims.json").read_text()):
            if "real" in c["claim"]:
                shown.append({"n": c["n"], "claim": f"checked: {c['claim']}", "expected": "5", "confidence": "high"})
                (folder / f"finding_{c['n']}.py").write_text(SHOWN)
            elif "silent" not in c["claim"]:
                not_shown.append({"n": c["n"], "reason": "the claim is false"})
        (folder / "findings.json").write_text(json.dumps(shown))
        (folder / "not_shown.json").write_text(json.dumps(not_shown))
        with self.lock:
            self.calls.append({"kind": "import", "model": graph["defaults"]["model"], "adapter": graph["defaults"]["adapter"],
                               "folder": str(folder), "graph": graph})
        return {"status": "done", "steps": [{"node": "work", "ok": True, "verdict": "PASS", "seconds": 3, "cost_usd": 0.1}],
                "jobs": ["j"], "cost_usd": 0.1, "seconds": 3}


class ImportCase(FlowCase):
    def setUp(self) -> None:
        super().setUp()
        self.runner = ImportRunner()

    def write(self, data: Any, name: str = "outside.json") -> str:
        path = Path(self._tmp.name) / name
        path.write_text(json.dumps(data))
        return str(path)

    def imports(self) -> Dict[str, Any]:
        return json.loads((self.out / "imports.json").read_text())


class ImportTest(ImportCase):
    def test_a_claim_gets_a_repro_then_two_verifiers_and_the_gate(self):
        self.init()
        file = self.write([{"file": "pkg/mod.py", "function": "add", "claim": "real: add subtracts", "source": "tool A"},
                           {"file": "pkg/mod.py", "line": 3, "claim": "add is slow"}])
        code, r = self.hpf("import", "--findings", file, "--source", "tool B")
        self.assertEqual(code, 0, r)
        self.assertEqual((r["claims"], r["runs"], r["grade_1"], len(r["not_shown"]), r["grade_0"], r["skipped"]), (2, 1, 1, 1, [], []))
        # The two claims are about one function, so one worker session has them.
        self.assertEqual(self.runner.count("import"), 1)
        rows = {f["n"]: f for f in self.imports()["findings"]}
        self.assertEqual((rows[1]["grade"], rows[1]["result"], rows[1]["source"], rows[1]["outside_claim"]),
                         (1, "-1", "tool A", "real: add subtracts"))
        self.assertEqual((rows[2]["grade"], rows[2]["source"], rows[2]["not_shown"]), (0, "tool B", True))
        self.assertIn("the claim is false", rows[2]["reason"])
        # No targets and no review: the import is the source of the findings.
        code, status = self.hpf("status")
        self.assertEqual(status["not_done"], ["verify: not run"])
        self.assertEqual(status["steps"]["import"]["runs"], 1)
        code, r = self.hpf("verify")
        self.assertEqual(code, 0, r)
        self.assertEqual((r["claims"], r["confirmed_bugs"]), (1, 1))
        bug = json.loads((self.out / "confirmed.json").read_text())[0]
        self.assertEqual((bug["function"], bug["sources"]), ("add", ["tool A"]))
        self.assertIn("| tool A |", (self.out / "REPORT.md").read_text())
        code, gate = self.hpf("gate")
        self.assertEqual((gate["verdict"], gate["incomplete"], len(gate["open"])), ("fail", [], 1))
        # The repro of the imported claim gives a new result on a commit with the fix.
        (self.repo / "pkg" / "mod.py").write_text((self.repo / "pkg" / "mod.py").read_text().replace("return a - b", "return a + b", 1))
        self.git_commit("fix")
        code, gate = self.hpf("gate", "--ref", "HEAD")
        self.assertEqual((code, gate["verdict"], gate["closed"]), (0, "pass", 1))

    def git_commit(self, message: str) -> None:
        from test_hpflow import git
        git(self.repo, "commit", "-q", "-am", message)

    def test_an_imported_finding_and_a_review_finding_of_one_function_go_to_one_verifier_session(self):
        self.through_verify()
        verify_runs = self.runner.count("verify")
        file = self.write([{"file": "pkg/mod.py", "function": "add", "claim": "real: another input"}])
        self.assertEqual(self.hpf("import", "--findings", file)[0], 0)
        # The new finding has no verdict, so the audit is not complete and the gate fails.
        code, status = self.hpf("status")
        self.assertIn("verify: 1 findings have no verdict (run `verify` again)", status["not_done"])
        self.assertEqual(self.hpf("gate")[1]["verdict"], "fail")
        code, r = self.hpf("verify")
        self.assertEqual(code, 0, r)
        self.assertEqual(self.runner.count("verify"), verify_runs + 2)
        claims = json.loads((self.out / "verify.json").read_text())["claims"]
        self.assertEqual({c["target"] for c in claims}, {claims[0]["target"]})
        self.assertEqual(sorted({c["source"] for c in claims}), ["hpf review", "outside"])
        self.assertNotIn("verify: 1 findings have no verdict (run `verify` again)", self.hpf("status")[1]["not_done"])

    def test_a_claim_with_no_answer_is_a_failed_run(self):
        self.init()
        file = self.write([{"file": "pkg/mod.py", "function": "add", "claim": "silent"}])
        code, r = self.hpf("import", "--findings", file)
        self.assertEqual(code, 1, r)
        self.assertEqual(r["failed_runs"][0]["error"], "no answer for claim 1")
        self.assertEqual(r["grade_0"][0]["reason"], "the worker gave no answer for this claim")
        code, status = self.hpf("status")
        self.assertIn("import: 1 runs failed", status["not_done"])
        self.assertEqual(self.hpf("gate")[1]["verdict"], "fail")

    def test_an_entry_that_the_ladder_cannot_take_is_skipped_with_a_reason(self):
        self.init()
        (self.out / "src" / "pkg" / "twice.py").write_text("def f():\n    return 1\n\n\ndef f():\n    return 2\n\n\nclass C:\n    def m(self):\n        return 3\n")
        entries = [
            {"file": "pkg/mod.py", "function": "nope", "claim": "x"},
            {"file": "pkg/mod.py", "line": 4, "claim": "x"},
            {"file": "pkg/absent.py", "line": 1, "claim": "x"},
            {"file": "README.md", "line": 1, "claim": "x"},
            {"file": "tests/test_mod.py", "function": "test_sub", "claim": "x"},
            {"file": "../outside.py", "line": 1, "claim": "x"},
            {"file": "pkg/twice.py", "function": "f", "claim": "x"},
            {"file": "pkg/mod.py", "claim": "no place"},
            {"file": "pkg/mod.py", "function": "add", "claim": "  "},
            {"function": "add", "claim": "x"},
            "text",
            {"file": "pkg/mod.py", "function": "add", "line": True, "claim": "real: a boolean is not a line"},
            {"file": "pkg/twice.py", "function": "f", "line": 6, "claim": "real: the second f"},
            {"file": "pkg/twice.py", "function": "m", "claim": "real: a method with no class name"},
            {"file": "pkg/twice.py", "function": "old_name", "line": 10, "claim": "real: a method with no class name"},
            {"file": str(self.repo / "pkg" / "mod.py"), "function": "sub", "claim": "real: a full path"},
            {"file": "pkg\\mod.py", "function": "sub", "claim": "real: a full path"},
        ]
        code, r = self.hpf("import", "--findings", self.write(entries))
        self.assertEqual(code, 0, r)
        reasons = {s["index"]: s["reason"] for s in r["skipped"]}
        self.assertEqual(reasons[0], "no function nope in the file")
        self.assertEqual(reasons[1], "line 4 is in no function")
        self.assertIn("not in the snapshot", reasons[2])
        self.assertEqual(reasons[3], "not a Python file")
        self.assertEqual(reasons[4], "a test file")
        self.assertEqual(reasons[5], "the path is not inside the repository")
        self.assertEqual(reasons[6], "2 functions have the name f: give the line")
        self.assertEqual(reasons[7], "no function name and no line")
        self.assertEqual(reasons[8], "no claim text")
        self.assertEqual(reasons[9], "no file")
        self.assertEqual(reasons[10], "the entry is not an object")
        self.assertEqual(sorted(reasons), list(range(11)))
        # The ladder did not judge the skipped entries, and the gate report says how many there are.
        self.hpf("verify")
        self.assertEqual(self.hpf("gate")[1]["outside_claims"], {"taken": 4, "skipped": 11})
        claims = {(c["file"], c["function"]) for c in self.imports()["claims"]}
        self.assertEqual(claims, {("pkg/mod.py", "add"), ("pkg/twice.py", "f"), ("pkg/twice.py", "C.m"), ("pkg/mod.py", "sub")})
        # The same claim for one function, in two path forms, is one claim.
        self.assertEqual(r["claims"], 4)
        second = [f for f in self.imports()["findings"] if f["file"] == "pkg/twice.py" and f["function"] == "f"]
        self.assertEqual(len(second), 1)

    def test_sarif_results_are_claims(self):
        self.init()
        sarif = {"version": "2.1.0", "runs": [{"tool": {"driver": {"name": "scan"}}, "results": [
            {"ruleId": "R1", "message": {"text": "real: wrong sum"},
             "locations": [{"physicalLocation": {"artifactLocation": {"uri": "pkg/mod.py"}, "region": {"startLine": 2}}}]},
            {"message": {"text": "x"}, "locations": [{"physicalLocation": {"artifactLocation": {"uri": "pkg/mod.py"}}}]},
            {"message": {}, "locations": []},
            {"message": {"text": "real: a file address"},
             "locations": [{"physicalLocation": {"artifactLocation": {"uri": (self.repo / "pkg" / "mod.py").as_uri()},
                                                 "region": {"startLine": 7}}}]}]}]}
        code, r = self.hpf("import", "--findings", self.write(sarif, "scan.sarif"))
        self.assertEqual(code, 0, r)
        self.assertEqual({s["index"]: s["reason"] for s in r["skipped"]},
                         {1: "no start line in the first location", 2: "no message text"})
        rows = sorted(self.imports()["findings"], key=lambda f: f["function"])
        self.assertEqual([(f["function"], f["source"], f["outside_claim"]) for f in rows],
                         [("add", "scan", "R1: real: wrong sum"), ("sub", "scan", "real: a file address")])

    def test_a_file_that_is_not_a_findings_file_is_a_usage_error(self):
        self.init()
        for text in ("not json", '{"a": 1}', '"text"'):
            path = Path(self._tmp.name) / "bad.json"
            path.write_text(text)
            code, r = self.hpf("import", "--findings", str(path))
            self.assertEqual(code, 2, text)
            self.assertIn("findings file", r["usage_error"])
        code, r = self.hpf("import", "--findings", str(Path(self._tmp.name) / "absent.json"))
        self.assertEqual(code, 2)
        self.assertEqual(self.runner.calls, [])

    def test_a_second_call_reuses_the_stored_result(self):
        self.init()
        file = self.write([{"file": "pkg/mod.py", "function": "add", "claim": "real: add subtracts"}])
        self.hpf("import", "--findings", file)
        code, r = self.hpf("import", "--findings", file)
        self.assertEqual((r["worker_runs"], r["reused"], self.runner.count("import")), (0, 1, 1))

    def test_more_claims_than_one_session_takes_make_more_sessions(self):
        self.init()
        entries = [{"file": "pkg/mod.py", "function": "add", "claim": f"real: claim {k}"} for k in range(briefs.IMPORT_PART + 1)]
        code, r = self.hpf("import", "--findings", self.write(entries))
        self.assertEqual((code, r["claims"], r["runs"], r["grade_1"]), (0, briefs.IMPORT_PART + 1, 2, briefs.IMPORT_PART + 1))
        # The ids of the findings of the two sessions are not the same.
        self.assertEqual(len({f["id"] for f in self.imports()["findings"]}), briefs.IMPORT_PART + 1)


class AuditWithFindingsTest(ImportCase):
    def audit(self, *args: str) -> tuple:
        return self.hpf("audit", "--repo", str(self.repo), "--ref", "HEAD", "--python", sys.executable, *args)

    def test_an_audit_of_outside_findings_only(self):
        file = self.write([{"file": "pkg/mod.py", "function": "add", "claim": "real: add subtracts"}])
        code, r = self.audit("--findings", file)
        self.assertEqual(code, 0, r)
        self.assertEqual([s["command"] for s in r["steps"]], ["init", "import", "verify"])
        self.assertEqual(self.runner.count("review"), 0)
        self.assertEqual(self.hpf("status")[1]["not_done"], ["fix: 1 confirmed bugs have no accepted fix with a PASS judge"])

    def test_an_audit_with_a_review_and_outside_findings(self):
        file = self.write([{"file": "pkg/mod.py", "function": "add", "claim": "real: add subtracts"}])
        code, r = self.audit("--changed", "HEAD~1..HEAD", "--findings", file, "--repro-timeout", "2")
        self.assertEqual(code, 0, r)
        self.assertEqual([s["command"] for s in r["steps"]], ["init", "targets", "review", "import", "verify"])

    def test_a_bad_findings_file_stops_the_audit_before_a_worker_runs(self):
        path = Path(self._tmp.name) / "bad.json"
        path.write_text("not json")
        code, r = self.audit("--changed", "HEAD~1..HEAD", "--findings", str(path))
        self.assertEqual(code, 2, r)
        self.assertEqual(self.runner.calls, [])
        self.assertFalse((self.out / "audit.json").exists())

    def test_an_audit_needs_targets_or_findings(self):
        code, r = self.audit()
        self.assertEqual((code, r["usage_error"]), (2, "audit needs --changed, --function, --file or --findings"))


class OutsideFormTest(unittest.TestCase):
    def read(self, data: Any) -> tuple:
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            path = Path(tmp) / "f.json"
            path.write_text(data if isinstance(data, str) else json.dumps(data), encoding="utf-8")
            return outside.read(path, "tool")

    def test_the_two_forms_of_the_hpflow_list(self):
        one = {"file": "a.py", "function": "f", "claim": "c"}
        for data in ([one], {"findings": [one]}, "\ufeff" + json.dumps([one])):
            entries, skipped = self.read(data)
            self.assertEqual((entries, skipped), ([{"index": 0, "file": "a.py", "function": "f", "line": None, "claim": "c", "source": "tool"}], []))

    def test_a_long_claim_is_cut(self):
        entries, _ = self.read([{"file": "a.py", "line": 1, "claim": "x" * (outside.MAX_CLAIM + 10)}])
        self.assertEqual(len(entries[0]["claim"]), outside.MAX_CLAIM)

    def test_the_path_of_a_sarif_address(self):
        self.assertEqual(outside.file_of_uri("pkg/a%20b.py"), "pkg/a b.py")
        self.assertEqual(outside.file_of_uri("file:///repo/pkg/a%20b.py"), "/repo/pkg/a b.py")
        self.assertEqual(outside.file_of_uri("file:///C:/repo/a.py"), "C:/repo/a.py")
        self.assertEqual(outside.file_of_uri("C:\\repo\\a.py"), "C:\\repo\\a.py")
        self.assertEqual(outside.file_of_uri("https://example.com/a.py"), "https://example.com/a.py")

    def test_a_file_that_cannot_be_read_is_a_usage_error(self):
        with self.assertRaises(UsageError):
            outside.read(Path(tempfile.gettempdir()) / "hpflow-no-such-file.json")


class BriefTextTest(unittest.TestCase):
    """The reviewer briefs are the texts of the study. A change of their text changes what the measured numbers
    are about, so it must be a decision."""

    def test_the_review_and_verify_briefs_did_not_change(self):
        import hashlib
        pins = {"REVIEW": "87cb1cba2c739fafd5982dbba27b5158cb075bcbb62c5a6e26802ae5eda30982",
                "REVIEW_FILE": "04c8a93d3cb7d22cabd39663023802abbde25e3557b24197993bd1fc4be438fc",
                "VERIFY": "cf98e6aefd85fd45786c8e86d8b6ea5e2106b29c2a2c36661a077429c48820fc"}
        for name, pin in pins.items():
            self.assertEqual(hashlib.sha256(getattr(briefs, name).encode("utf-8")).hexdigest(), pin, name)

    def test_the_import_brief_has_each_field(self):
        text = briefs.IMPORT.format(n=2, function="f", file="pkg/m.py", root="project/", top="pkg", arm_text="")
        self.assertNotIn("{", text.replace('{"n"', "").replace("}", ""))
        self.assertIn(briefs.RUN_FILE.format(root="project/", top="pkg"), text)


if __name__ == "__main__":
    unittest.main()
