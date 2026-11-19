"""Tests of hpflow. A FakeRunner writes the files that a worker would write. No test makes a model call."""
from __future__ import annotations

import io
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from typing import Any, Dict, List

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow.cli import build_parser, main  # noqa: E402
from hpflow.common import apply_cost_rule, run_group, run_snippet  # noqa: E402
from hpflow.runner import PuppetmasterRunner, Runner  # noqa: E402

MOD_A = '''def add(a, b):
    """Return the sum of a and b."""
    return a + b


def sub(a, b):
    return a - b


def gone(x):
    return x


def long_one(x):
    y = x
    return y
'''

LONG_BODY = "".join(f"    y = y + {i}\n" for i in range(200))
MOD_B = MOD_A.replace("return a + b", "return a - b").replace(
    "def gone(x):\n    return x\n\n\n", "").replace("    y = x\n", "    y = x\n" + LONG_BODY)

TEST_A = '''import unittest

from pkg.mod import sub


class SubTest(unittest.TestCase):
    def test_sub(self):
        self.assertEqual(sub(3, 1), 2)
'''
TEST_B = TEST_A + '''
    def test_sub_zero(self):
        self.assertEqual(sub(0, 0), 0)
'''

REPROS = {
    1: "def run():\n    from pkg.mod import add\n    return repr(add(2, 3))\n",
    2: "def run():\n    from pkg.mod import missing_name\n    return repr(missing_name())\n",
    3: "def run():\n    while True:\n        pass\n",
    4: "def run():\n    from pkg.mod import add\n    return repr(add(1, 1))\n",
    5: "def run():\n    from pkg.mod import add\n    return repr(add(0, 0))\n",
}

NEW_TEST = '''import unittest

from pkg.mod import add


class AddTest(unittest.TestCase):
    def test_add(self):
        self.assertEqual(add(2, 3), 5)

    def test_add_zero(self):
        self.assertEqual(add(0, 0), 0)
'''

OPUS, SONNET = "claude-opus-5-5", "claude-sonnet-5-5"


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@localhost", *args],
                          check=True, capture_output=True, text=True).stdout.strip()


class FakeRunner(Runner):
    """Writes the files of a reviewer, a verifier or a fix worker, and counts the runs."""

    def __init__(self) -> None:
        self.calls: List[Dict[str, Any]] = []
        self.lock = threading.Lock()
        self.first_verdict = "real"

    def run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        model = graph["defaults"]["model"]
        if graph["entry"] == "build":
            kind = "fix"
            mod = folder / "pkg" / "mod.py"
            mod.write_text(mod.read_text().replace("return a - b", "return a + b", 1))
            (folder / "tests" / "test_hpfix_pkg_mod.py").write_text(NEW_TEST)
            steps = [{"node": "build", "ok": True, "verdict": "PASS", "seconds": 5, "cost_usd": 0.3},
                     {"node": "check", "ok": True}, {"node": "review", "ok": True, "verdict": "PASS", "seconds": 2,
                                                     "cost_usd": 0.1}]
        elif (folder / "claims.json").exists():
            kind = "verify"
            claims = json.loads((folder / "claims.json").read_text())
            out = []
            for c in claims:
                if model == SONNET:
                    v = {"k": c["k"], "verdict": self.first_verdict, "duplicate_of": 1 if c["k"] == 2 else None,
                         "what_goes_wrong": "add subtracts", "caller": "pkg/mod.py:1", "fix_idea": "use +"}
                else:
                    v = {"k": c["k"], "verdict": "intended" if c["k"] == 3 else "real", "duplicate_of": None}
                out.append(v)
            (folder / "verdicts.json").write_text(json.dumps(out))
            steps = [{"node": "work", "ok": True, "verdict": "PASS", "seconds": 4, "cost_usd": 0.2}]
        else:
            kind = "review"
            assert (folder / "project" / "pkg" / "mod.py").exists()
            findings = [{"n": n, "claim": f"claim {n}", "expected": "5", "confidence": "high"} for n in REPROS]
            if (folder / "functions.json").exists():
                names = json.loads((folder / "functions.json").read_text())
                if len(names) > 1:
                    findings = [dict(findings[0], function=names[0]), dict(findings[3], function=names[1]),
                                dict(findings[4], function="not_in_the_list")]
                else:
                    findings = [dict(f, function=names[0]) for f in findings]
            (folder / "findings.json").write_text(json.dumps(findings))
            for n, text in REPROS.items():
                (folder / f"finding_{n}.py").write_text(text)
            steps = [{"node": "work", "ok": True, "verdict": "PASS", "seconds": 3, "cost_usd": 0.1}]
        with self.lock:
            self.calls.append({"kind": kind, "model": model, "folder": str(folder), "graph": graph})
        return {"status": "done", "steps": steps, "jobs": ["j"], "cost_usd": sum(s.get("cost_usd", 0) for s in steps),
                "seconds": sum(s.get("seconds", 0) for s in steps)}

    def count(self, kind: str) -> int:
        return sum(1 for c in self.calls if c["kind"] == kind)


class FlowCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="hpflow-")
        root = Path(self._tmp.name)
        self.repo = root / "repo"
        (self.repo / "pkg").mkdir(parents=True)
        (self.repo / "tests").mkdir()
        (self.repo / "pkg" / "__init__.py").write_text("")
        (self.repo / "pkg" / "mod.py").write_text(MOD_A)
        (self.repo / "tests" / "test_mod.py").write_text(TEST_A)
        git(self.repo, "init", "-q", "-b", "main")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "a")
        (self.repo / "pkg" / "mod.py").write_text(MOD_B)
        (self.repo / "tests" / "test_mod.py").write_text(TEST_B)
        git(self.repo, "commit", "-q", "-am", "b")
        self.out = (root / "audit").resolve()
        self.runner = FakeRunner()

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def hpf(self, *args: str) -> tuple:
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main([*args, "--out", str(self.out)], runner=self.runner)
        return code, json.loads(buf.getvalue())

    def init(self) -> None:
        code, r = self.hpf("init", "--repo", str(self.repo), "--ref", "HEAD", "--test-cmd", "{python} -m unittest {tests}",
                           "--python", sys.executable)
        self.assertEqual(code, 0, r)
        self.assertEqual(r["audit"]["paths"], ["pkg", "tests"])

    def through_verify(self) -> None:
        self.init()
        self.assertEqual(self.hpf("targets", "--changed", "HEAD~1..HEAD")[0], 0)
        code, r = self.hpf("review", "--repro-timeout", "2")
        self.assertEqual(code, 0, r)
        code, r = self.hpf("verify")
        self.assertEqual(code, 0, r)


class TargetsTest(FlowCase):
    def test_changed(self):
        self.init()
        code, r = self.hpf("targets", "--changed", "HEAD~1..HEAD")
        self.assertEqual(code, 0, r)
        self.assertEqual(r["targets"], ["pkg/mod.py:add"])
        reasons = {(s["file"], s["function"]): s["reason"] for s in r["skipped"]}
        self.assertTrue(reasons[("pkg/mod.py", "long_one")].startswith("too long"))
        self.assertEqual(reasons[("tests/test_mod.py", "SubTest.test_sub_zero")], "test file")
        self.assertEqual(reasons[("pkg/mod.py", "gone")], "removed")
        self.assertNotIn(("pkg/mod.py", "sub"), reasons)

    def test_named_and_usage_error(self):
        self.init()
        code, r = self.hpf("targets", "--function", "pkg/mod.py:sub")
        self.assertEqual((code, r["targets"]), (0, ["pkg/mod.py:sub"]))
        code, r = self.hpf("targets", "--function", "pkg/mod.py:nothing")
        self.assertEqual(code, 2, r)


class FixCheckTest(unittest.TestCase):
    def test_a_very_large_related_test_file_is_not_run(self):
        from hpflow import fixcheck

        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            tree, info = Path(tmp) / "tree", Path(tmp) / "info"
            (tree / "pkg").mkdir(parents=True)
            (tree / "tests").mkdir()
            info.mkdir()
            (tree / "pkg" / "__init__.py").write_text("")
            (tree / "pkg" / "mod.py").write_text("def add(a, b):\n    return a + b\n")
            ok = "import unittest\nfrom pkg.mod import add\n\n\nclass T(unittest.TestCase):\n    def test_add(self):\n        self.assertEqual(add(1, 2), 3)\n"
            (tree / "tests" / "test_hpfix_pkg_mod.py").write_text(ok)
            (tree / "tests" / "test_mod_small.py").write_text(ok)
            big = ok.replace("add(1, 2), 3", "add(1, 2), 4") + "# pad\n" * (fixcheck.MAX_RELATED_BYTES // 6 + 10)
            (tree / "tests" / "test_mod_big.py").write_text(big)
            (info / "spec.json").write_text(json.dumps({"file": "pkg/mod.py", "test_file": "tests/test_hpfix_pkg_mod.py", "python": sys.executable,
                                                        "test_cmd": "{python} -m unittest {tests}", "bugs": []}))
            result = fixcheck.check(info, tree)
        self.assertEqual(result["verdict"], "accept", result)
        self.assertEqual(result["large_test_files_not_run"], ["tests/test_mod_big.py"])


class LadderTest(FlowCase):
    def test_review_grades(self):
        self.init()
        self.hpf("targets", "--changed", "HEAD~1..HEAD")
        code, r = self.hpf("review", "--repro-timeout", "2")
        self.assertEqual(code, 0, r)
        self.assertEqual(self.runner.count("review"), 1)
        findings = {f["n"]: f for f in json.loads((self.out / "review.json").read_text())["findings"]}
        self.assertEqual(findings[1]["grade"], 1)
        self.assertEqual(findings[1]["result"], "-1")
        self.assertEqual(findings[2]["grade"], 0)
        self.assertIn("ImportError", findings[2]["reason"])
        self.assertEqual(findings[3]["grade"], 0)
        self.assertIn("timed out", findings[3]["reason"])
        self.assertEqual(r["grade_1"], 3)

    def test_verify_grades_and_duplicates(self):
        self.through_verify()
        self.assertEqual(self.runner.count("verify"), 2)
        self.assertEqual({c["model"] for c in self.runner.calls if c["kind"] == "verify"}, {OPUS, SONNET})
        claims = {c["k"]: c for c in json.loads((self.out / "verify.json").read_text())["claims"]}
        self.assertEqual(claims[1]["grade"], 2)
        self.assertEqual(claims[2]["grade"], 2)
        self.assertEqual(claims[2]["duplicate_of"], 1)
        self.assertEqual(claims[3]["grade"], 1)
        self.assertEqual(claims[3]["class"], "mixed")
        bugs = json.loads((self.out / "confirmed.json").read_text())
        self.assertEqual(len(bugs), 1)
        self.assertEqual(bugs[0]["claims"], [1, 2])
        report = (self.out / "REPORT.md").read_text()
        for title in ("## Confirmed (2)", "## Real but not reachable (0)", "## By design (0)", "## Mixed (1)"):
            self.assertIn(title, report)

    def test_fix(self):
        self.through_verify()
        before = git(self.repo, "rev-list", "--all")
        head = git(self.repo, "rev-parse", "HEAD")
        code, r = self.hpf("fix")
        self.assertEqual(code, 0, r)
        self.assertEqual(len(r["worktrees"]), 1)
        w = r["worktrees"][0]
        self.assertTrue(Path(w["worktree"]).is_dir())
        self.assertEqual(Path(w["worktree"]), self.out / "fix" / "pkg-mod")
        self.assertEqual(git(self.repo, "rev-parse", "hpfix/pkg-mod"), head)
        self.assertIn("pkg/mod.py", w["diffstat"])
        self.assertIn("tests/test_hpfix_pkg_mod.py", w["new_files"])
        self.assertEqual(w["check"], "accept", w)
        self.assertEqual(w["judge"], "PASS")
        self.assertEqual(git(self.repo, "rev-list", "--all"), before)
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), head)
        self.assertEqual(git(self.repo, "status", "--porcelain"), "")
        code, s = self.hpf("status")
        self.assertEqual(code, 0, s)
        self.assertEqual(s["grades"], {"0": 2, "1": 1, "2": 0, "3": 2})
        self.assertEqual(s["not_done"], [])

    def bug_id(self) -> str:
        return json.loads((self.out / "confirmed.json").read_text())[0]["id"]

    def test_gate_fails_before_the_review(self):
        self.init()
        self.hpf("targets", "--changed", "HEAD~1..HEAD")
        code, r = self.hpf("gate")
        self.assertEqual((code, r["verdict"]), (1, "fail"))
        self.assertIn("review: not run", r["incomplete"])

    def test_gate_fails_on_an_open_bug_and_passes_after_an_accepted_fix(self):
        self.through_verify()
        code, r = self.hpf("gate")
        self.assertEqual((code, r["verdict"], len(r["open"])), (1, "fail", 1))
        self.assertEqual(self.hpf("fix")[0], 0)
        calls = len(self.runner.calls)
        code, r = self.hpf("gate")
        self.assertEqual((code, r["verdict"], r["closed"], r["open"]), (0, "pass", 1, []))
        self.assertEqual(len(self.runner.calls), calls)

    def test_gate_with_a_ref_needs_a_new_repro_result_on_that_commit(self):
        self.through_verify()
        self.assertEqual(self.hpf("fix")[0], 0)
        code, r = self.hpf("gate", "--ref", "HEAD", "--repro-timeout", "5")
        self.assertEqual((code, r["verdict"]), (1, "fail"), r)
        self.assertIn("old result", r["open"][0]["reason"])
        mod = self.repo / "pkg" / "mod.py"
        mod.write_text(mod.read_text().replace("return a - b", "return a + b", 1))
        git(self.repo, "commit", "-q", "-am", "fix add")
        code, r = self.hpf("gate", "--ref", "HEAD", "--repro-timeout", "5")
        self.assertEqual((code, r["verdict"], r["closed"]), (0, "pass", 1), r)
        self.assertNotEqual(r["checked_commit"], r["audited_commit"])

    def test_a_repro_that_does_not_run_on_the_ref_keeps_the_bug_open(self):
        self.through_verify()
        mod = self.repo / "pkg" / "mod.py"
        mod.write_text(mod.read_text().replace("def add(", "def plus("))
        git(self.repo, "commit", "-q", "-am", "rename")
        code, r = self.hpf("gate", "--ref", "HEAD", "--repro-timeout", "5")
        self.assertEqual((code, len(r["open"])), (1, 1), r)
        self.assertIn("does not run", r["open"][0]["reason"])

    def test_a_range_with_no_changed_function_passes_the_gate_with_no_worker(self):
        self.init()
        code, r = self.hpf("targets", "--changed", "HEAD..HEAD")
        self.assertEqual((code, r["targets"]), (0, []), r)
        self.assertEqual(self.hpf("review")[0], 0)
        code, r = self.hpf("gate", "--ref", "HEAD")
        self.assertEqual((code, r["verdict"], r["targets"], r["confirmed_bugs"]), (0, "pass", 0, 0), r)
        self.assertEqual(self.runner.calls, [])

    def test_one_reviewer_session_for_the_functions_of_one_file(self):
        self.init()
        code, r = self.hpf("targets", "--function", "pkg/mod.py:add", "pkg/mod.py:sub")
        self.assertEqual((code, len(r["targets"])), (0, 2), r)
        code, r = self.hpf("review", "--repro-timeout", "2", "--group", "file")
        self.assertEqual((code, r["group"]), (0, "file"), r)
        self.assertEqual(self.runner.count("review"), 1)
        findings = json.loads((self.out / "review.json").read_text())["findings"]
        self.assertEqual(sorted((f["n"], f["function"]) for f in findings), [(1, "add"), (4, "sub")])
        self.assertEqual(self.hpf("status")[1]["not_done"], ["verify: not run"])
        code, r = self.hpf("verify")
        self.assertEqual((code, r["groups"], self.runner.count("verify")), (0, 1, 2), r)
        claims = json.loads((self.out / "verify.json").read_text())["claims"]
        self.assertEqual({c["function"] for c in claims}, {"add", "sub"})

    def test_one_session_for_each_function_and_each_verifier_on_request(self):
        self.init()
        self.hpf("targets", "--function", "pkg/mod.py:add", "pkg/mod.py:sub")
        code, r = self.hpf("review", "--repro-timeout", "2")
        self.assertEqual((code, r["group"], self.runner.count("review")), (0, "function", 2), r)
        self.assertEqual(self.runner.calls[0]["graph"]["nodes"][0]["payload"]["extra_args"][:2], ["--setting-sources", ""])
        self.runner.first_verdict = "intended"
        code, r = self.hpf("verify", "--all-verifiers")
        self.assertEqual((code, r["group"], r["groups"], self.runner.count("verify")), (0, "function", 2, 4), r)

    def test_the_second_verifier_runs_only_where_the_first_says_real(self):
        self.init()
        self.hpf("targets", "--changed", "HEAD~1..HEAD")
        self.assertEqual(self.hpf("review", "--repro-timeout", "2")[0], 0)
        self.runner.first_verdict = "intended"
        code, r = self.hpf("verify")
        self.assertEqual((code, r["staged"], self.runner.count("verify")), (0, True, 1), r)
        self.assertEqual({c["model"] for c in self.runner.calls if c["kind"] == "verify"}, {SONNET})
        self.assertEqual(r["classes"], {"by_design": 3})
        self.assertEqual(r["confirmed_bugs"], 0)
        code, g = self.hpf("gate", "--ref", "HEAD")
        self.assertEqual((code, g["verdict"]), (0, "pass"), g)

    def test_a_worker_gets_the_user_settings_only_on_request(self):
        self.init()
        self.hpf("targets", "--changed", "HEAD~1..HEAD")
        self.assertEqual(self.hpf("review", "--repro-timeout", "2", "--user-settings")[0], 0)
        self.assertNotIn("extra_args", self.runner.calls[0]["graph"]["nodes"][0]["payload"])

    def test_waive(self):
        self.through_verify()
        bug = self.bug_id()
        self.assertEqual(self.hpf("waive", "--bug", "nothing", "--reason", "x")[0], 2)
        self.assertEqual(self.hpf("waive", "--bug", bug, "--reason", "  ")[0], 2)
        code, r = self.hpf("waive", "--bug", bug, "--reason", "the owner accepts this behavior", "--by", "owner")
        self.assertEqual(code, 0, r)
        code, r = self.hpf("gate", "--ref", "HEAD")
        self.assertEqual((code, r["verdict"], r["waived"]), (0, "pass", 1), r)
        self.assertEqual(r["bugs"][0]["reason"], "the owner accepts this behavior")

    def test_second_call_reuses_and_redo_runs(self):
        self.through_verify()
        self.assertEqual(self.hpf("fix")[0], 0)
        counts = (self.runner.count("review"), self.runner.count("verify"), self.runner.count("fix"))
        self.assertEqual(counts, (1, 2, 1))
        self.init()
        for cmd in (["targets", "--changed", "HEAD~1..HEAD"], ["review", "--repro-timeout", "2"], ["verify"], ["fix"]):
            code, r = self.hpf(*cmd)
            self.assertEqual(code, 0, r)
            self.assertEqual(r.get("worker_runs", 0), 0, cmd)
        code, r = self.hpf("audit", "--repo", str(self.repo), "--ref", "HEAD", "--changed", "HEAD~1..HEAD",
                           "--repro-timeout", "2", "--test-cmd", "{python} -m unittest {tests}", "--python", sys.executable)
        self.assertEqual(code, 0, r)
        self.assertEqual((self.runner.count("review"), self.runner.count("verify"), self.runner.count("fix")), counts)
        self.assertEqual(self.hpf("review", "--repro-timeout", "2", "--redo")[1]["worker_runs"], 1)
        self.assertEqual(self.hpf("verify", "--redo")[1]["worker_runs"], 2)
        code, r = self.hpf("fix", "--redo")
        self.assertEqual((code, r["worker_runs"]), (0, 1), r)
        self.assertEqual((self.runner.count("review"), self.runner.count("verify"), self.runner.count("fix")), (2, 4, 2))

    def test_run_folder_names(self):
        self.through_verify()
        banned = ["test", "eval", "bug", "add", "sub", "long_one", "gone"]
        names = [p.name for p in (self.out / "runs").iterdir()]
        self.assertEqual(len(names), 3)
        for c in self.runner.calls:
            self.assertEqual(Path(c["folder"]).parent, self.out / "runs")
        for name in names:
            for word in banned:
                self.assertNotIn(word, name.lower())
            self.assertRegex(name, r"^[0-9]+$")


FAKE_PM = r'''#!/usr/bin/env python3
import json, sys
a = sys.argv[1:]
if a[:2] == ["flow", "run"]:
    print(json.dumps({"run_id": "flow-1"}))
elif a[:2] == ["flow", "wait"]:
    print(json.dumps({"status": "done", "steps": [
        {"node": "work", "ok": True, "verdict": "FAIL", "job_ids": ["j1"]},
        {"node": "check", "ok": False},
        {"node": "work", "ok": True, "verdict": "PASS", "job_ids": ["j2"]}]}))
elif a[0] == "status":
    print(json.dumps({"job": {"created_at": "2026-01-01T00:00:00", "completed_at": "2026-01-01T00:00:10"}}))
elif a[0] == "artifacts":
    print('{"total_cost_usd": %s}' % {"j1": "0.4", "j2": "0.5"}[a[1]])
'''


class CostTest(unittest.TestCase):
    def test_rule(self):
        steps = [{"node": "work", "reported_usd": 0.4}, {"node": "work", "reported_usd": 0.5}]
        nodes = apply_cost_rule(steps)
        self.assertAlmostEqual(nodes["work"], 0.5)
        self.assertAlmostEqual(steps[0]["cost_usd"], 0.4)
        self.assertAlmostEqual(steps[1]["cost_usd"], 0.1)

    def test_puppetmaster_runner_with_a_fake_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "bin").mkdir()
            pm = root / "bin" / "puppetmaster"
            pm.write_text(FAKE_PM.replace("#!/usr/bin/env python3", "#!" + sys.executable))
            pm.chmod(0o755)
            old = os.environ["PATH"]
            os.environ["PATH"] = f"{root / 'bin'}{os.pathsep}{old}"
            try:
                graph = {"id": "hpf-1", "entry": "work", "defaults": {"timeout_seconds": 60}, "nodes": [], "edges": []}
                r = PuppetmasterRunner(root / "graphs").run(graph, root / "w")
            finally:
                os.environ["PATH"] = old
            self.assertEqual(r["status"], "done", r)
            self.assertAlmostEqual(r["cost_usd"], 0.5)
            visits = [s for s in r["steps"] if s["node"] == "work"]
            self.assertAlmostEqual(visits[1]["cost_usd"], 0.1)
            self.assertEqual(r["jobs"], ["j1", "j2"])
            self.assertEqual(r["seconds"], 20)
            self.assertTrue((root / "graphs" / "hpf-1.json").exists())
            self.assertTrue(re.match(r"^flow-1$", r["flow"]))


def gone(pid: int, seconds: float = 5) -> bool:
    """True when the process `pid` ends within `seconds`."""
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return True
        time.sleep(0.05)
    return False


class ProcessGroupTest(unittest.TestCase):
    def test_timeout_ends_the_whole_group(self):
        start = time.monotonic()
        code, out, _ = run_group(["/bin/sh", "-c", "sleep 30 & echo $!; wait"], timeout=1)
        self.assertIsNone(code)
        self.assertLess(time.monotonic() - start, 10)
        self.assertTrue(gone(int(out.split()[0])), "the child of the command still runs after the timeout")

    def test_a_child_left_after_a_normal_exit_ends(self):
        code, out, _ = run_group(["/bin/sh", "-c", "sleep 30 >/dev/null 2>&1 & echo $!"], timeout=10)
        self.assertEqual(code, 0)
        self.assertTrue(gone(int(out.split()[0])))

    def test_repro_timeout_ends_its_children(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pidfile = root / "pid"
            snippet = root / "s.py"
            snippet.write_text("def run():\n    import subprocess, time\n"
                               f"    p = subprocess.Popen(['/bin/sleep', '30'])\n"
                               f"    open({str(pidfile)!r}, 'w').write(str(p.pid))\n"
                               "    time.sleep(30)\n")
            got = run_snippet(root, snippet, root / "home", timeout=2)
            self.assertEqual(got["error"], "timeout")
            self.assertTrue(gone(int(pidfile.read_text())))


class ConcurrencyTest(unittest.TestCase):
    def test_default_is_five(self):
        self.assertEqual(PuppetmasterRunner(Path("/nonexistent")).concurrency, 5)
        args = build_parser().parse_args(["review", "--out", "/nonexistent"])
        self.assertEqual(args.concurrency, 5)

    def test_runner_limits_parallel_flows(self):
        runner = PuppetmasterRunner(Path("/nonexistent"), concurrency=2)
        lock, live, peak = threading.Lock(), [0], [0]

        def fake(graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
            with lock:
                live[0] += 1
                peak[0] = max(peak[0], live[0])
            time.sleep(0.2)
            with lock:
                live[0] -= 1
            return {"status": "done"}

        runner._run = fake  # type: ignore[method-assign]
        threads = [threading.Thread(target=runner.run, args=({}, Path("/nonexistent"))) for _ in range(6)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        self.assertEqual(peak[0], 2)

    def test_concurrency_zero_is_a_usage_error(self):
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main(["status", "--out", "/nonexistent", "--concurrency", "0"], runner=FakeRunner())
        self.assertEqual(code, 2)


if __name__ == "__main__":
    unittest.main()
