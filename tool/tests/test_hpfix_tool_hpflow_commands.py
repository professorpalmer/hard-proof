"""Regression tests of the confirmed bugs in hpflow/commands.py. No test makes a model call or uses the network."""
from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow import adapters, commands  # noqa: E402
from hpflow.cli import main  # noqa: E402
from hpflow.common import UsageError  # noqa: E402

ENV = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
           GIT_COMMITTER_EMAIL="t@t", GIT_CONFIG_GLOBAL=os.devnull)


def git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True, env=ENV)


def make_repo(root: Path, files: dict) -> Path:
    repo = root / "repo"
    for name, text in files.items():
        (repo / name).parent.mkdir(parents=True, exist_ok=True)
        (repo / name).write_text(text)
    git(repo, "init", "-q", "-b", "main")
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "-m", "a")
    return repo


class SlugTest(unittest.TestCase):
    def test_a_path_that_is_not_a_module_path_does_not_take_the_slug_of_one(self):
        self.assertNotEqual(commands.slug_of("pkg/a-b.py"), commands.slug_of("pkg/a/b.py"))

    def test_unique_slugs_of_paths_with_the_same_plain_slug_differ(self):
        slugs = {commands.slug_of(f, unique=True) for f in ("pkg/a_b.py", "pkg/a-b.py", "pkg/a/b.py", "pkg/A/b.py")}
        self.assertEqual(len(slugs), 4)

    def test_a_module_path_keeps_its_old_slug(self):
        self.assertEqual(commands.slug_of("pkg/mod.py"), "pkg-mod")
        self.assertEqual(commands.slug_of("tool/hpflow/commands.py"), "tool-hpflow-commands")
        self.assertEqual(commands.slug_of("hpflow/fix_check.py"), "hpflow-fix-check")
        self.assertEqual(commands.slug_of("pkg/My_mod.py"), "pkg-my-mod")


class FixRunner:
    def run(self, graph, folder):
        return {"status": "pass", "steps": []}


class FixGroupTest(unittest.TestCase):
    def fix(self, files: list) -> list:
        with tempfile.TemporaryDirectory() as t:
            root = Path(t)
            repo = make_repo(root, {f: "def f():\n    return 1\n" for f in files})
            out = root / "out"
            out.mkdir()
            rep = root / "repro.py"
            rep.write_text("def run():\n    return 1\n")
            head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, capture_output=True, text=True).stdout.strip()
            (out / "audit.json").write_text(json.dumps({"repo": str(repo), "commit": head, "paths": ["pkg"],
                                                        "python": sys.executable, "test_cmd": "{python} {tests}"}))
            bugs = [{"id": f"b{i}", "file": f, "function": "f", "claims": [1], "claim": "x", "result_now": "1",
                     "what_goes_wrong": "x", "caller": "x", "fix_idea": "x",
                     "repros": [{"finding": f"r{i}", "k": 1, "path": str(rep), "result_now": "1"}]}
                    for i, f in enumerate(files)]
            (out / "confirmed.json").write_text(json.dumps(bugs))
            rep_out = commands.cmd_fix(commands.Context(out, FixRunner()), None, None, None, None, None)
            return [(w["slug"], w["bugs"]) for w in rep_out["worktrees"]]

    def test_two_files_with_one_plain_slug_get_two_worktrees(self):
        rows = self.fix(["pkg/a_b.py", "pkg/a/b.py"])
        self.assertEqual(sorted(b for _, b in rows), [["b0"], ["b1"]])
        self.assertEqual(len({s for s, _ in rows}), 2)

    def test_a_file_with_no_twin_keeps_its_plain_slug(self):
        self.assertEqual(self.fix(["pkg/a_b.py"]), [("pkg-a-b", ["b0"])])


class DeletionTest(unittest.TestCase):
    def targets(self, old: str, new: str) -> list:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            repo = make_repo(root, {"pkg/__init__.py": "", "pkg/m.py": old})
            (repo / "pkg" / "m.py").write_text(new)
            git(repo, "commit", "-q", "-am", "b")
            out = str((root / "audit").resolve())

            def hpf(*args: str) -> dict:
                buf = io.StringIO()
                with redirect_stdout(buf):
                    main([*args, "--out", out])
                return json.loads(buf.getvalue())
            hpf("init", "--repo", str(repo), "--ref", "HEAD", "--python", sys.executable)
            return hpf("targets", "--changed", "HEAD~1..HEAD")["targets"]

    def test_a_deleted_blank_line_between_functions_changes_no_function(self):
        old = "def f():\n    return 1\n\n\ndef g():\n    return 2\n"
        new = "def f():\n    return 1\n\ndef g():\n    return 2\n"
        self.assertEqual(self.targets(old, new), [])

    def test_a_deleted_line_in_a_function_still_changes_it(self):
        old = "def f():\n    x = 1\n    return 1\n\n\ndef g():\n    return 2\n"
        new = "def f():\n    return 1\n\n\ndef g():\n    return 2\n"
        self.assertEqual(self.targets(old, new), ["pkg/m.py:f"])

    def test_a_deleted_last_line_and_a_deleted_decorator_still_change_their_functions(self):
        old = "def f():\n    x = 1\n    return x\n\n\n@staticmethod\ndef g():\n    return 2\n"
        new = "def f():\n    x = 1\n\n\ndef g():\n    return 2\n"
        self.assertEqual(self.targets(old, new), ["pkg/m.py:f", "pkg/m.py:g"])


class AdapterKeyTest(unittest.TestCase):
    def test_the_effort_is_not_part_of_the_key_of_the_command_adapter(self):
        self.assertEqual(commands.adapter_key(adapters.COMMAND, "mytool run", "high"),
                         commands.adapter_key(adapters.COMMAND, "mytool run", "medium"))

    def test_the_effort_stays_in_the_key_of_the_other_adapters(self):
        self.assertEqual(commands.adapter_key(adapters.DEFAULT_ADAPTER, None, "high"), ["effort=high"])
        self.assertEqual(commands.adapter_key(adapters.DEFAULT_ADAPTER, None, adapters.DEFAULT_EFFORT), [])


class NoRunner:
    def run(self, graph, folder):
        return {"seconds": 0, "cost_usd": 0.0}


class VerifyKeyTest(unittest.TestCase):
    def ids(self, efforts: tuple) -> list:
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "out"
            (out / "src").mkdir(parents=True)
            (out / "audit.json").write_text(json.dumps({"commit": "abc", "repo": "/r/repo"}))
            rep = Path(d) / "repro.py"
            rep.write_text("def run():\n    return 1\n")
            f = {"id": "1", "grade": 1, "file": "a.py", "target": "a.py::f", "function": "f", "run": "r", "n": 1,
                 "claim": "x", "expected": "y", "result": "z", "repro": str(rep)}
            (out / "review.json").write_text(json.dumps({"findings": [f]}))
            ids = []
            for effort in efforts:
                commands.cmd_verify(commands.Context(out, NoRunner(), effort=effort), ["sonnet", "opus"], staged=False)
                ids.append(sorted(json.loads((out / "verify.json").read_text())["runs"]))
            return ids

    def test_another_effort_gives_other_verify_records(self):
        low, high = self.ids(("low", "high"))
        self.assertFalse(set(low) & set(high))

    def test_the_same_effort_gives_the_same_verify_records(self):
        a, b = self.ids(("high", "high"))
        self.assertEqual(a, b)


GETTER_SETTER = ("class C:\n    @property\n    def x(self):\n        return 1\n\n"
                 "    @x.setter\n    def x(self, v):\n        pass\n")


class TargetIdTest(unittest.TestCase):
    """The identity of a function is its file, its qualified name and its number among the definitions of that name."""

    def test_the_parser_numbers_the_definitions_of_one_name(self):
        fns = commands.functions_of(GETTER_SETTER + "\n\ndef f():\n    pass\n")
        self.assertEqual([(f["function"], f["nth"], f["of"]) for f in fns], [("C.x", 1, 2), ("C.x", 2, 2), ("f", 1, 1)])

    def test_a_getter_and_a_setter_are_two_targets(self):
        getter, setter = (commands.make_target("pkg/m.py", fn, "file") for fn in commands.functions_of(GETTER_SETTER))
        self.assertNotEqual(getter["id"], setter["id"])
        # The first definition keeps the id of hpflow 0.4, so an audit folder of 0.4 keeps its stored runs.
        self.assertEqual(getter["id"], commands.digest("target", "pkg/m.py", "C.x"))

    def test_a_record_with_no_identity_is_not_a_target(self):
        # A record that does not come from the parser has no `nth`, so it cannot get the id of another function.
        with self.assertRaises(KeyError):
            commands.make_target("pkg/m.py", {"function": "C.x", "start": 3, "end": 5}, "file")

    def test_one_function_named_twice_is_one_target(self):
        fn = commands.functions_of("def f():\n    pass\n")[0]
        self.assertEqual(commands.make_target("pkg/m.py", fn, "file")["id"],
                         commands.make_target("pkg/m.py", dict(fn), "function")["id"])

    def test_targets_lists_the_getter_and_the_setter(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d)
            (out / "src" / "pkg").mkdir(parents=True)
            (out / "src" / "pkg" / "m.py").write_text(GETTER_SETTER)
            (out / "audit.json").write_text(json.dumps({"commit": "abc", "repo": d, "paths": ["pkg"]}))
            rep = commands.cmd_targets(commands.Context(out, None), None, None, ["pkg/m.py"], 100, None)
            self.assertEqual(rep["targets"], ["pkg/m.py:C.x", "pkg/m.py:C.x"])
            targets = json.loads((out / "targets.json").read_text())["targets"]
            self.assertEqual(len({x["id"] for x in targets}), 2)
            rep = commands.cmd_targets(commands.Context(out, None), None, ["pkg/m.py:C.x"], ["pkg/m.py"], 100, None)
            self.assertEqual(len(rep["targets"]), 2)
            # A worker must know which of the two definitions is its target.
            self.assertEqual(commands.target_label(targets[1]), "C.x (definition 2 of 2 with this name, at line 6)")
            self.assertEqual(commands.target_label({"function": "f", "of": 1}), "f")


class FixCheckCommandTest(unittest.TestCase):
    """The check of a fix is a file `check.py`, so a folder name with a quote or an apostrophe cannot break it."""

    def script_path(self, folder: str) -> str:
        old = commands.TOOL_DIR
        commands.TOOL_DIR = Path(folder)
        try:
            code = compile(commands.check_script(Path("info dir")), "<check>", "exec")
        finally:
            commands.TOOL_DIR = old
        return next(c for c in code.co_consts if isinstance(c, str) and "hpflow" in c and "fixcheck" not in c)

    def test_a_folder_with_an_apostrophe_compiles(self):
        self.assertEqual(self.script_path("C:/Users/O'Brien/hpflow"), str(Path("C:/Users/O'Brien/hpflow")))

    def test_backslashes_stay_backslashes(self):
        folder = "C:\\Users\\ann\\new\\hpflow"
        self.assertEqual(self.script_path(folder), str(Path(folder)))

    def test_the_command_is_one_plain_python_call(self):
        cmd = commands.fixcheck_command(Path("/tmp/info"))
        self.assertTrue(cmd.endswith("check.py"), cmd)
        self.assertNotIn("PYTHONPATH", cmd)


class InitTest(unittest.TestCase):
    def init(self, files: list):
        with tempfile.TemporaryDirectory() as t:
            repo = make_repo(Path(t), {f: "" for f in files})
            ctx = commands.Context(Path(t) / "out", None)
            return commands.cmd_init(ctx, str(repo), "HEAD", None, None, None)["audit"]["paths"]

    def test_no_package_folder_is_a_usage_error_even_with_tests_and_readme(self):
        with self.assertRaises(UsageError):
            self.init(["src/pkg/__init__.py", "tests/test_a.py", "README.md"])

    def test_a_package_folder_keeps_the_extra_paths(self):
        self.assertEqual(self.init(["pkg/__init__.py", "tests/test_a.py", "README.md"]), ["pkg", "tests", "README.md"])


class CountingRunner:
    def __init__(self):
        self.n = 0

    def run(self, graph, folder):
        self.n += 1
        Path(folder, "findings.json").write_text("[]")
        return {"status": "pass"}


class ShortPromptTest(unittest.TestCase):
    def runs(self, first: bool, second: bool) -> tuple:
        with tempfile.TemporaryDirectory() as d:
            out = Path(d)
            (out / "src").mkdir()
            (out / "audit.json").write_text(json.dumps({"commit": "abc", "paths": ["."]}))
            t = {"id": "1", "file": "m.py", "function": "f", "top": "m", "lines": [1, 2]}
            (out / "targets.json").write_text(json.dumps({"targets": [t]}))
            r = CountingRunner()
            ctx = commands.Context(out, r)
            commands.cmd_review(ctx, None, False, 1, 5, short_prompt=first)
            rep = commands.cmd_review(ctx, None, False, 1, 5, short_prompt=second)
            return rep["worker_runs"], rep["reused"], r.n

    def test_the_short_prompt_does_not_reuse_default_prompt_records(self):
        self.assertEqual(self.runs(False, True), (1, 0, 2))

    def test_the_same_prompt_reuses_its_records(self):
        self.assertEqual(self.runs(False, False), (0, 1, 1))
        self.assertEqual(self.runs(True, True), (0, 1, 1))


class CountFixRunner:
    def __init__(self):
        self.n = 0

    def run(self, graph, folder):
        self.n += 1
        return {"status": "pass", "steps": []}


class FixKeyTest(unittest.TestCase):
    """A fix run is reused only for the same model, judge model and rules."""

    def runs(self, first: tuple, second: tuple) -> int:
        with tempfile.TemporaryDirectory() as t:
            root = Path(t)
            repo = make_repo(root, {"pkg/a.py": "def f():\n    return 1\n"})
            out = root / "out"
            out.mkdir()
            rep = root / "repro.py"
            rep.write_text("def run():\n    return 1\n")
            head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, capture_output=True, text=True).stdout.strip()
            (out / "audit.json").write_text(json.dumps({"repo": str(repo), "commit": head, "paths": ["pkg"],
                                                        "python": sys.executable, "test_cmd": "{python} {tests}"}))
            bugs = [{"id": "b0", "file": "pkg/a.py", "function": "f", "claims": [1], "claim": "x", "result_now": "1",
                     "what_goes_wrong": "x", "caller": "x", "fix_idea": "x",
                     "repros": [{"finding": "r0", "k": 1, "path": str(rep), "result_now": "1"}]}]
            (out / "confirmed.json").write_text(json.dumps(bugs))
            runner = CountFixRunner()
            ctx = commands.Context(out, runner)
            commands.cmd_fix(ctx, None, None, *first)
            commands.cmd_fix(ctx, None, None, *second)
            return runner.n

    def test_another_model_judge_model_or_rules_starts_a_worker(self):
        self.assertEqual(self.runs(("opus", None, None), ("sonnet", None, None)), 2)
        self.assertEqual(self.runs(("opus", "sonnet", None), ("opus", "opus", None)), 2)
        self.assertEqual(self.runs(("opus", None, None), ("opus", None, "other rules")), 2)

    def test_the_same_settings_reuse_the_fix(self):
        self.assertEqual(self.runs(("opus", None, None), ("opus", None, None)), 1)
        self.assertEqual(self.runs(("opus", None, "r"), ("opus", None, "r")), 1)


class FixGraphTestCommandTest(unittest.TestCase):
    def task(self, py: str) -> str:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            ctx = type("C", (), {"lean": False, "effort": adapters.DEFAULT_EFFORT, "src": tmp})()
            audit = {"python": py, "test_cmd": "{python} -m pytest {tests}", "repo": str(tmp), "paths": ["src"]}
            g = {"bugs": [], "slug": "s", "file": "src/a.py", "test_file": "tests/test_a.py"}
            graph = commands.fix_graph(ctx, audit, g, "base", tmp / "info", adapters.DEFAULT_ADAPTER, None, "m", "j", "r")
            return graph["nodes"][0]["task"]

    def test_a_python_path_with_a_space_is_quoted(self):
        py = "/opt/my python/bin/python"
        self.assertIn(commands.shell_quote(py) + " -m pytest", self.task(py))
        self.assertNotIn(py + " -m pytest", self.task(py))

    def test_a_plain_python_path_stays_as_it_was(self):
        self.assertIn("/usr/bin/python3 -m pytest tests/test_a.py", self.task("/usr/bin/python3"))


class InitNameTest(unittest.TestCase):
    def init(self, files: list):
        with tempfile.TemporaryDirectory() as t:
            repo = make_repo(Path(t), {f: "" for f in files})
            ctx = commands.Context(Path(t) / "out", None)
            return commands.cmd_init(ctx, str(repo), "HEAD", None, None, None)["audit"]["paths"]

    def test_a_package_with_a_non_ascii_name_is_found(self):
        self.assertEqual(self.init(["pkg_é/__init__.py"]), ["pkg_é"])
        self.assertEqual(self.init(["a/__init__.py", "pkg_é/__init__.py"]), ["a", "pkg_é"])

    def test_ascii_packages_keep_their_paths(self):
        self.assertEqual(self.init(["a/__init__.py", "b/__init__.py", "c/x.py"]), ["a", "b"])


class DiffContentLineTest(unittest.TestCase):
    """A content line '-- x' or '++ x' of a hunk is shown as '--- x' or '+++ x' and is not a file header."""

    def test_a_content_line_that_looks_like_a_header_is_not_read(self):
        d = "diff --git a/a.py b/a.py\n--- a/a.py\n+++ b/a.py\n@@ -3 +3 @@\n--- old\n+++ new\n-@@ -9 +9 @@\n"
        self.assertEqual(commands.hunk_ranges(d), {"old_ranges": [(3, 3)], "new_ranges": [(3, 3)], "deleted_ranges": []})

    def test_targets_finds_a_function_changed_only_by_a_deleted_dash_line(self):
        old = 'def f():\n    q = """\n-- keep\n-- drop\nselect 1\n"""\n    return q\n\n\ndef g():\n    return 2\n'
        self.assertEqual(DeletionTest().targets(old, old.replace("-- drop\n", "")), ["pkg/m.py:f"])

    def test_targets_of_a_plain_deleted_line_stay(self):
        old = 'def f():\n    q = """\n-- keep\nselect 1\ndrop\n"""\n    return q\n\n\ndef g():\n    return 2\n'
        self.assertEqual(DeletionTest().targets(old, old.replace("drop\n", "")), ["pkg/m.py:f"])


class FileChunkReviewTest(unittest.TestCase):
    def rows(self, n_functions: int, named: str, count: int) -> list:
        with tempfile.TemporaryDirectory() as d:
            out = Path(d)
            (out / "src").mkdir()
            (out / "audit.json").write_text(json.dumps({"commit": "abc", "paths": ["."]}))
            targets = [{"id": f"t{i}", "file": "a.py", "function": f"f{i}", "top": "a", "lines": [i * 10, i * 10 + 5]}
                       for i in range(1, n_functions + 1)]
            (out / "targets.json").write_text(json.dumps({"targets": targets}))
            last = f"f{n_functions}"

            class Runner:
                def run(self, graph, folder):
                    names = json.loads((folder / "functions.json").read_text())
                    items = [{"n": i, "function": named, "claim": "c", "expected": "e", "confidence": "high"}
                             for i in range(1, count + 1)] if names == [last] else []
                    (folder / "findings.json").write_text(json.dumps(items))
                    return {"status": "pass"}

            commands.cmd_review(commands.Context(out, Runner()), None, False, 1, 5, group="file", group_size=6)
            rows = json.loads((out / "review.json").read_text())["findings"]
            return sorted((r["function"], r["n"]) for r in rows)

    def test_a_one_function_chunk_drops_findings_on_other_functions(self):
        self.assertEqual(self.rows(7, "f1", 5), [])

    def test_a_one_function_chunk_keeps_the_per_function_cap(self):
        from hpflow import briefs
        self.assertEqual(len(self.rows(7, "f7", 8)), briefs.PER_FUNCTION)

    def test_a_one_function_chunk_keeps_findings_on_its_function(self):
        self.assertEqual(self.rows(1, "f1", 2), [("f1", 1), ("f1", 2)])


if __name__ == "__main__":
    unittest.main()
