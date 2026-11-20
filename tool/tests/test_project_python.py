"""The repros run with the Python of the project under audit, not with the Python of hpflow.

The ladder test makes a real second venv with `python -m venv`. The venv holds a module that the Python of hpflow
cannot import, and the code under audit imports it."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

TOOL = Path(__file__).resolve().parent.parent
TESTS = Path(__file__).resolve().parent
for p in (TOOL, TESTS):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

from hpflow import adapters, common  # noqa: E402
from hpflow.direct import DirectRunner  # noqa: E402
from hpflow.runner import agent_graph  # noqa: E402
from hpflow.common import UsageError  # noqa: E402
from test_hpflow import MOD_A, MOD_B, TEST_A, TEST_B, FakeRunner, FlowCase, git  # noqa: E402

DEP = "hpflow_dependency_only_in_the_venv"


def venv_bin(venv: Path) -> Path:
    return venv / "Scripts" / "python.exe" if os.name == "nt" else venv / "bin" / "python"


def make_venv(venv: Path) -> Path:
    """A real venv with no pip (fast), and the module DEP in its site-packages."""
    subprocess.run([sys.executable, "-m", "venv", "--without-pip", str(venv)], check=True, capture_output=True)
    py = venv_bin(venv)
    purelib = subprocess.run([str(py), "-I", "-c", "import sysconfig; print(sysconfig.get_paths()['purelib'])"],
                             check=True, capture_output=True, text=True).stdout.strip()
    (Path(purelib) / f"{DEP}.py").write_text("VALUE = 7\n")
    # Python 3.13 and later write this file. An older Python does not, and git must not see the venv.
    (venv / ".gitignore").write_text("*\n")
    return py


class VenvLadderTest(FlowCase):
    """The code under audit imports a module that only the venv of the project has."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="hpflow-")
        root = Path(self._tmp.name)
        self.repo = root / "repo"
        (self.repo / "pkg").mkdir(parents=True)
        (self.repo / "tests").mkdir()
        (self.repo / "pkg" / "__init__.py").write_text("")
        head = f"import {DEP}\n\n\n"
        (self.repo / "pkg" / "mod.py").write_text(head + MOD_A)
        (self.repo / "tests" / "test_mod.py").write_text(TEST_A)
        git(self.repo, "init", "-q", "-b", "main")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "a")
        (self.repo / "pkg" / "mod.py").write_text(head + MOD_B)
        (self.repo / "tests" / "test_mod.py").write_text(TEST_B)
        git(self.repo, "commit", "-q", "-am", "b")
        self.venv_python = make_venv(self.repo.resolve() / ".venv")
        self.out = (root / "audit").resolve()
        self.runner = FakeRunner()

    def test_the_python_of_hpflow_cannot_import_the_dependency(self):
        p = subprocess.run([sys.executable, "-I", "-c", f"import {DEP}"], capture_output=True, text=True)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("ModuleNotFoundError", p.stderr)
        p = subprocess.run([str(self.venv_python), "-I", "-c", f"import {DEP}; print({DEP}.VALUE)"],
                           capture_output=True, text=True)
        self.assertEqual((p.returncode, p.stdout.strip()), (0, "7"), p.stderr)

    def test_review_verify_gate_and_fix_run_the_repros_in_the_venv(self):
        # No --python: the default is the venv of the repository.
        code, r = self.hpf("init", "--repo", str(self.repo), "--ref", "HEAD", "--test-cmd", "{python} -m unittest {tests}")
        self.assertEqual(code, 0, r)
        self.assertEqual(r["audit"]["python"], str(self.venv_python))
        self.assertEqual(self.hpf("targets", "--changed", "HEAD~1..HEAD")[0], 0)
        code, r = self.hpf("review", "--repro-timeout", "20")
        self.assertEqual(code, 0, r)
        findings = {f["n"]: f for f in json.loads((self.out / "review.json").read_text())["findings"]}
        self.assertEqual(findings[1]["grade"], 1, findings[1])
        self.assertEqual(findings[1]["result"], "-1")
        code, r = self.hpf("verify")
        self.assertEqual(code, 0, r)
        self.assertEqual(len(json.loads((self.out / "confirmed.json").read_text())), 1)
        # The gate runs the repro on the commit: it gives the old result, so the repro ran to an answer.
        code, r = self.hpf("gate", "--ref", "HEAD", "--repro-timeout", "20")
        self.assertEqual((code, r["verdict"]), (1, "fail"), r)
        self.assertIn("old result", r["open"][0]["reason"])
        # The fix check runs the repros and the tests of the fix in the venv too.
        code, r = self.hpf("fix")
        self.assertEqual(code, 0, r)
        self.assertEqual(r["worktrees"][0]["check"], "accept", r)
        code, r = self.hpf("gate")
        self.assertEqual((code, r["verdict"]), (0, "pass"), r)
        # Each worker graph names the Python of the project, and no allow list names it: the shell name stays python3.
        for call in self.runner.calls:
            self.assertEqual(call["graph"]["defaults"]["python"], str(self.venv_python), call["kind"])
            if call["kind"] != "fix":
                payload = json.dumps([n.get("payload") for n in call["graph"]["nodes"]])
                self.assertNotIn(str(self.venv_python), payload, call["kind"])
                self.assertIn("python3", payload, call["kind"])
        review = next(c for c in self.runner.calls if c["kind"] == "review")
        self.assertEqual(review["graph"]["nodes"][0]["payload"], adapters.payload("claude-code", shell=True))


@unittest.skipIf(os.name == "nt", "the worker command is a POSIX shell line")
class WorkerShimTest(unittest.TestCase):
    """`python3` and `python` in the shell of a worker are the Python of the project."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="hpflow-")
        self.root = Path(self._tmp.name).resolve()
        self.out = self.root / "audit"

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def run_worker(self, line: str, python):
        payload = adapters.payload("command", agent_cmd=f"sh -c {line!r}")
        graph = agent_graph("hpf-1", "task", [], "command", "m", payload, python=python)
        folder = self.root / "work"
        return DirectRunner(self.out / "graphs").run(graph, folder), folder

    def test_a_command_worker_imports_a_dependency_of_the_venv(self):
        venv_python = make_venv(self.root / "venv")
        line = (f"python3 -c 'import {DEP}; print({DEP}.VALUE)' > a.txt && "
                f"python -c 'import {DEP}, sys; print(sys.prefix)' > b.txt && echo VERDICT: PASS")
        r, folder = self.run_worker(line, str(venv_python))
        self.assertEqual(r["status"], "done", r)
        self.assertEqual((folder / "a.txt").read_text().strip(), "7")
        self.assertEqual(Path((folder / "b.txt").read_text().strip()).resolve(), (self.root / "venv").resolve())
        self.assertEqual((self.out / "bin" / "python3").read_text(), common.shim_texts(str(venv_python), False)["python3"])
        # The same command with no Python of the project cannot import the module.
        r, _ = self.run_worker(line, None)
        self.assertEqual(r["status"], "failed", r)

    def test_with_the_python_of_hpflow_the_worker_path_is_as_before(self):
        line = 'printf "%s" "$PATH" > path.txt && echo VERDICT: PASS'
        r, folder = self.run_worker(line, sys.executable)
        self.assertEqual(r["status"], "done", r)
        self.assertEqual((folder / "path.txt").read_text(), os.environ.get("PATH", ""))
        self.assertFalse((self.out / "bin").exists())

    def test_a_path_with_a_space_and_a_quote(self):
        target = self.root / "it's a venv" / "python"
        target.parent.mkdir()
        os.symlink(sys.executable, target)
        r, folder = self.run_worker("python3 -c 'import sys; print(sys.version_info[0])' > v.txt && echo VERDICT: PASS",
                                    str(target))
        self.assertEqual(r["status"], "done", r)
        self.assertEqual((folder / "v.txt").read_text().strip(), "3")


class ShimTextTest(unittest.TestCase):
    def test_the_text_of_each_shim(self):
        posix = common.shim_texts("/a b/.venv/bin/python", False)
        self.assertEqual(posix, {"python3": "#!/bin/sh\nexec '/a b/.venv/bin/python' \"$@\"\n",
                                 "python": "#!/bin/sh\nexec '/a b/.venv/bin/python' \"$@\"\n"})
        win = common.shim_texts(r"C:\p 100%\.venv\Scripts\python.exe", True)
        line = '@"C:\\p 100%%\\.venv\\Scripts\\python.exe" %*\r\n'
        self.assertEqual(win, {"python3.cmd": line, "python.cmd": line})

    def test_write_keeps_a_right_file_and_replaces_a_wrong_one(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            folder = Path(tmp) / "bin"
            common.write_python_shims(folder, "/x/python")
            names = sorted(p.name for p in folder.iterdir())
            self.assertEqual(names, sorted(common.shim_texts("/x/python", common.WINDOWS)))
            first = folder / names[0]
            if not common.WINDOWS:
                self.assertTrue(os.access(first, os.X_OK))
            common.write_python_shims(folder, "/y/python")
            self.assertIn("/y/python", first.read_text())
            self.assertEqual(sorted(p.name for p in folder.iterdir()), names)

    def test_a_right_cmd_shim_is_not_written_again(self):
        # The local audit confirmed this bug: the text check read the CRLF of a .cmd file as LF, so each worker
        # start replaced both files, also while another worker ran them.
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp, mock.patch.object(common, "WINDOWS", True):
            folder = Path(tmp) / "bin"
            common.write_python_shims(folder, r"C:\v\python.exe")
            before = {p.name: p.stat().st_ino for p in folder.iterdir()}
            common.write_python_shims(folder, r"C:\v\python.exe")
            self.assertEqual({p.name: p.stat().st_ino for p in folder.iterdir()}, before)
            self.assertEqual((folder / "python3.cmd").read_bytes(), b'@"C:\\v\\python.exe" %*\r\n')


class StoredPythonTest(FlowCase):
    def test_an_audit_with_no_python_is_a_usage_error(self):
        self.through_verify()
        audit = json.loads((self.out / "audit.json").read_text())
        del audit["python"]
        (self.out / "audit.json").write_text(json.dumps(audit))
        code, r = self.hpf("gate", "--ref", "HEAD")
        self.assertEqual(code, 2, r)
        self.assertIn("--python", r["usage_error"])
        code, r = self.hpf("review")
        self.assertEqual(code, 2, r)
        self.assertIn("--python", r["usage_error"])

    def test_a_stored_python_that_is_gone_is_a_usage_error(self):
        self.through_verify()
        audit = json.loads((self.out / "audit.json").read_text())
        gone = str(Path(self._tmp.name) / "old-venv" / "bin" / "python")
        audit["python"] = gone
        (self.out / "audit.json").write_text(json.dumps(audit))
        for args in (("gate", "--ref", "HEAD"), ("review",), ("fix",)):
            code, r = self.hpf(*args)
            self.assertEqual(code, 2, (args, r))
            self.assertIn(gone, r["usage_error"])
            self.assertIn("--python", r["usage_error"])
        # A gate with no --ref runs no repro, so it does not need the Python.
        self.assertEqual(self.hpf("gate")[1]["verdict"], "fail")
        # A new init with --python repairs the audit folder.
        code, r = self.hpf("init", "--repo", str(self.repo), "--ref", "HEAD", "--python", sys.executable)
        self.assertEqual(code, 0, r)
        self.assertEqual(self.hpf("gate", "--ref", "HEAD")[0], 1)

    def test_the_fix_check_rejects_a_python_that_is_gone(self):
        from hpflow import fixcheck

        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            tree, info = Path(tmp) / "tree", Path(tmp) / "info"
            (tree / "pkg").mkdir(parents=True)
            info.mkdir()
            (tree / "pkg" / "__init__.py").write_text("")
            gone = str(Path(tmp) / "nothing" / "python")
            (info / "spec.json").write_text(json.dumps({"file": "pkg/mod.py", "test_file": "tests/t.py", "python": gone,
                                                        "test_cmd": "{python} -m unittest {tests}", "bugs": []}))
            result = fixcheck.check(info, tree)
        self.assertEqual(result["verdict"], "reject")
        self.assertIn(gone, result["problems"][0])


class InitPythonTest(FlowCase):
    def test_a_bare_name_is_stored_as_an_absolute_path(self):
        folder, name = os.path.split(sys.executable)
        # The folder is first on PATH, so the name finds this Python. git stays on PATH.
        with mock.patch.dict(os.environ, {"PATH": folder + os.pathsep + os.environ.get("PATH", "")}):
            code, r = self.hpf("init", "--repo", str(self.repo), "--ref", "HEAD", "--python", name)
        self.assertEqual(code, 0, r)
        self.assertEqual(r["audit"]["python"], os.path.join(os.path.abspath(folder), name))

    def test_a_python_that_does_not_exist_is_a_usage_error(self):
        code, r = self.hpf("init", "--repo", str(self.repo), "--ref", "HEAD",
                           "--python", str(Path(self._tmp.name) / "no" / "python"))
        self.assertEqual(code, 2, r)
        self.assertIn("--python", r["usage_error"])
        self.assertFalse((self.out / "audit.json").exists())

    @unittest.skipIf(os.name == "nt", "a POSIX program that is not Python")
    def test_a_program_that_is_not_python_3_is_a_usage_error(self):
        true = shutil.which("true")
        code, r = self.hpf("init", "--repo", str(self.repo), "--ref", "HEAD", "--python", true)
        self.assertEqual(code, 2, r)
        self.assertIn("not Python 3", r["usage_error"])

    def test_with_no_venv_the_default_is_the_python_of_hpflow(self):
        code, r = self.hpf("init", "--repo", str(self.repo), "--ref", "HEAD")
        self.assertEqual(code, 0, r)
        self.assertEqual(r["audit"]["python"], sys.executable)


class ImportRootPackageTest(unittest.TestCase):
    """The audit job in CI confirmed this bug: the names of the extra paths (tests, docs) are names at the
    repository root. Below --import-root, a package with such a name is a package of the product."""

    def test_a_package_named_tests_or_docs_below_the_import_root_is_audited(self):
        from hpflow import commands

        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            repo = Path(tmp) / "repo"
            for d in ("src/pkg", "src/docs", "src/tests"):
                (repo / d).mkdir(parents=True)
                (repo / d / "__init__.py").write_text("")
            (repo / "tests").mkdir()
            (repo / "tests" / "test_x.py").write_text("")
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            ctx = commands.Context(Path(tmp) / "out", None)
            r = commands.cmd_init(ctx, str(repo), "HEAD", None, sys.executable, None, "src")
            self.assertEqual(r["audit"]["paths"], ["src/docs", "src/pkg", "src/tests", "tests"])


class VenvLayoutTest(unittest.TestCase):
    def test_the_venv_python_of_each_platform(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            root = Path(tmp)
            self.assertIsNone(common.venv_python(root))
            win = root / ".venv" / "Scripts" / "python.exe"
            posix = root / ".venv" / "bin" / "python"
            for p in (win, posix):
                p.parent.mkdir(parents=True)
                p.write_text("")
            with mock.patch.object(common, "WINDOWS", True):
                self.assertEqual(common.venv_python(root), win)
            with mock.patch.object(common, "WINDOWS", False):
                self.assertEqual(common.venv_python(root), posix)
            win.unlink()
            with mock.patch.object(common, "WINDOWS", True):
                self.assertIsNone(common.venv_python(root))

    def test_project_python_needs_a_value_and_a_file(self):
        with self.assertRaises(UsageError) as e:
            common.project_python(None)
        self.assertIn("--python", str(e.exception))
        with self.assertRaises(UsageError):
            common.project_python("/no/such/python")
        self.assertEqual(common.project_python(sys.executable), sys.executable)


if __name__ == "__main__":
    unittest.main()
