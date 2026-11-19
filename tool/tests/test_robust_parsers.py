"""Tests of the readers that take text from outside hpflow: git names and diffs, the Codex config, test imports.

Each one had a parser of our own that failed on a new input form in each audit. Each now uses a form that has
no such cases: the NUL-separated name list of git, literal git paths, one rule for the end of a line, a scanner
that knows TOML strings, and the Python parser.
"""
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

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from hpflow import commands, fixcheck  # noqa: E402
from hpflow.cli import main  # noqa: E402
from hpflow.codexhome import first_key, lean_config, toml_scan  # noqa: E402
from hpflow.common import UsageError, git_status, lines_of, run_snippet  # noqa: E402
from hpflow.common import git as common_git  # noqa: E402
from hpflow.direct import parse_verdict  # noqa: E402
from hpflow.fixcheck import imports_module  # noqa: E402


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@localhost", *args],
                          check=True, capture_output=True, text=True).stdout


class ChangedFilesTest(unittest.TestCase):
    def test_names_with_a_space_and_a_non_ascii_letter_and_a_rename(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            repo = Path(tmp)
            (repo / "pkg").mkdir()
            body = "def f():\n    return 1\n\n\ndef g():\n    return 2\n"
            (repo / "pkg" / "my mod.py").write_text(body)
            (repo / "pkg" / "caf\u00e9.py").write_text(body, encoding="utf-8")
            (repo / "pkg" / "old.py").write_text(body + "\n\ndef h():\n    return 3\n")
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            (repo / "pkg" / "my mod.py").write_text(body.replace("return 1", "return 10"))
            (repo / "pkg" / "caf\u00e9.py").write_text(body.replace("return 2", "return 20"), encoding="utf-8")
            git(repo, "mv", "pkg/old.py", "pkg/new.py")
            (repo / "pkg" / "new.py").write_text((body + "\n\ndef h():\n    return 3\n").replace("return 3", "return 30"))
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "b")
            files = {(f["old"], f["new"]): f for f in commands.changed_files(repo, "HEAD~1", "HEAD", ["pkg"])}
            self.assertEqual(set(files), {("pkg/my mod.py", "pkg/my mod.py"), ("pkg/caf\u00e9.py", "pkg/caf\u00e9.py"),
                                          ("pkg/old.py", "pkg/new.py")})
            self.assertEqual(files[("pkg/my mod.py", "pkg/my mod.py")]["new_ranges"], [(2, 2)])
            self.assertEqual(files[("pkg/caf\u00e9.py", "pkg/caf\u00e9.py")]["new_ranges"], [(6, 6)])
            self.assertEqual(files[("pkg/old.py", "pkg/new.py")]["new_ranges"], [(10, 10)])


    def test_a_name_with_pattern_characters_selects_only_that_file(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            repo = Path(tmp)
            (repo / "pkg").mkdir()
            body = "def f():\n    return 1\n\n\ndef g():\n    return 2\n"
            # `a[b].py` as a git pattern also selects `ab.py`.
            (repo / "pkg" / "a[b].py").write_text(body)
            (repo / "pkg" / "ab.py").write_text(body)
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            (repo / "pkg" / "a[b].py").write_text(body.replace("return 1", "return 10"))
            (repo / "pkg" / "ab.py").write_text(body.replace("return 2", "return 20"))
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "b")
            files = {f["new"]: f for f in commands.changed_files(repo, "HEAD~1", "HEAD", ["pkg"])}
            self.assertEqual(files["pkg/a[b].py"]["new_ranges"], [(2, 2)])
            self.assertEqual(files["pkg/ab.py"]["new_ranges"], [(6, 6)])
            only = commands.changed_files(repo, "HEAD~1", "HEAD", ["pkg/a[b].py"])
            self.assertEqual([f["new"] for f in only], ["pkg/a[b].py"])


class LinesTest(unittest.TestCase):
    """Only a line feed ends a line. A form feed or U+2028 in outside text is content."""

    ODD = ("\x0b", "\x0c", "\x1c", "\x1d", "\x1e", "\x85", "\u2028", "\u2029")

    def test_only_a_line_feed_ends_a_line(self):
        self.assertEqual(lines_of("a\nb\n"), ["a", "b"])
        self.assertEqual(lines_of("a\n\nb"), ["a", "", "b"])
        self.assertEqual(lines_of(""), [])
        for ch in self.ODD:
            self.assertEqual(lines_of(f"a{ch}b\nc\n"), [f"a{ch}b", "c"], repr(ch))

    def test_a_changed_line_with_an_odd_character_is_not_a_hunk_header(self):
        for ch in self.ODD:
            d = f"diff --git a/a.py b/a.py\n--- a/a.py\n+++ b/a.py\n@@ -3 +3 @@\n-x = 1\n+x = '{ch}@@ -50 +50 @@'\n"
            self.assertEqual(commands.hunk_ranges(d), {"old_ranges": [(3, 3)], "new_ranges": [(3, 3)]}, repr(ch))

    def test_a_config_value_with_an_odd_character_stays_one_line(self):
        for ch in self.ODD:
            cfg = f'model = "m"\nnote = "a{ch}[mcp_servers.fake]"\nkeep = 1\n[hooks]\nx = 1\n[profiles.p]\ny = 2\n'
            self.assertEqual(lean_config(cfg), f'model = "m"\nnote = "a{ch}[mcp_servers.fake]"\nkeep = 1\n[profiles.p]\ny = 2\n',
                             repr(ch))

    def test_a_verdict_is_a_line_of_its_own(self):
        self.assertEqual(parse_verdict("done\nVERDICT: PASS - the check passes\n"), ("PASS", "the check passes"))
        for ch in ("\x85", "\u2028", "\u2029"):
            self.assertIsNone(parse_verdict(f"the file has this text: x{ch}VERDICT: PASS - ok"), repr(ch))
        # Only a space, a tab and a carriage return are space around the line.
        self.assertEqual(parse_verdict("done\r\n \tVERDICT: FAIL - no \r\n"), ("FAIL", "no"))
        for ch in self.ODD:
            self.assertIsNone(parse_verdict(f"done\n{ch}VERDICT: PASS - ok"), repr(ch))


class HunkRangesTest(unittest.TestCase):
    def test_a_hunk_gives_the_lines_it_removed_and_the_lines_it_added(self):
        d = "@@ -3,2 +3 @@\n-a\n-b\n+c\n@@ -9,0 +9,2 @@\n+d\n+e\n@@ -20,3 +21,0 @@\n-f\n-g\n-h\n"
        self.assertEqual(commands.hunk_ranges(d), {"old_ranges": [(3, 4), (20, 22)], "new_ranges": [(3, 3), (9, 10)]})


def diff_of(old: str, new: str) -> str:
    with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
        a, b = Path(tmp) / "a.py", Path(tmp) / "b.py"
        a.write_text(old)
        b.write_text(new)
        return subprocess.run(["git", "diff", "--no-index", "-U0", str(a), str(b)], capture_output=True, text=True).stdout


class ChangedTargetsTest(unittest.TestCase):
    def targets(self, old: str, new: str) -> dict:
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            root = Path(tmp)
            repo = root / "repo"
            (repo / "pkg").mkdir(parents=True)
            (repo / "pkg" / "__init__.py").write_text("")
            (repo / "pkg" / "m.py").write_text(old)
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            (repo / "pkg" / "m.py").write_text(new)
            git(repo, "commit", "-q", "-am", "b")
            out = str((root / "audit").resolve())

            def hpf(*args: str) -> dict:
                buf = io.StringIO()
                with redirect_stdout(buf):
                    main([*args, "--out", out])
                return json.loads(buf.getvalue())
            hpf("init", "--repo", str(repo), "--ref", "HEAD", "--python", sys.executable)
            return hpf("targets", "--changed", "HEAD~1..HEAD")

    def test_a_hunk_that_removes_the_end_of_a_function_and_adds_a_line_after_it(self):
        old = "def f():\n    x = 1\n    x += 1\n    return x\n\n\ndef g():\n    return 2\n"
        new = "def f():\n    x = 1\n# a comment\n\ndef g():\n    return 2\n"
        # The form that the audit found: one hunk removes lines of `f` and adds a line that is not in `f`.
        self.assertIn("@@ -3,3 +3 @@", diff_of(old, new))
        self.assertEqual(self.targets(old, new)["targets"], ["pkg/m.py:f"])

    def test_an_added_line_between_functions_changes_no_function(self):
        old = "def f():\n    return 1\n\n\ndef g():\n    return 2\n"
        new = "def f():\n    return 1\n\n# a comment\n\ndef g():\n    return 2\n"
        self.assertEqual(self.targets(old, new)["targets"], [])

    def test_a_removed_function_is_reported_and_its_neighbors_are_not_targets(self):
        old = "def f():\n    return 1\n\n\ndef h():\n    return 3\n\n\ndef g():\n    return 2\n"
        new = "def f():\n    return 1\n\n\ndef g():\n    return 2\n"
        got = self.targets(old, new)
        self.assertEqual(got["targets"], [])
        self.assertEqual(got["skipped"], [{"file": "pkg/m.py", "function": "h", "reason": "removed"}])

    def test_a_removed_second_definition_is_reported(self):
        old = ("class C:\n    @property\n    def v(self):\n        return 1\n\n    @v.setter\n    def v(self, x):\n"
               "        self.x = x\n\n    def w(self):\n        return 2\n")
        new = "class C:\n    @property\n    def v(self):\n        return 1\n\n    def w(self):\n        return 2\n"
        got = self.targets(old, new)
        self.assertEqual(got["targets"], [])
        self.assertEqual(got["skipped"], [{"file": "pkg/m.py", "function": "C.v", "reason": "removed"}])


class GitStatusTest(unittest.TestCase):
    def test_a_new_file_with_a_space_and_a_non_ascii_letter_has_its_real_name(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            repo = Path(tmp)
            (repo / "a.py").write_text("x = 1\n")
            (repo / "old.py").write_text("y = 1\ny = 2\ny = 3\n")
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            (repo / "my new.py").write_text("z = 1\n")
            (repo / "caf\u00e9.py").write_text("z = 2\n", encoding="utf-8")
            (repo / "a.py").write_text("x = 2\n")
            git(repo, "mv", "old.py", "new.py")
            entries = git_status(repo)
            self.assertEqual(sorted(e["path"] for e in entries if e["status"] == "??"), ["caf\u00e9.py", "my new.py"])
            self.assertIn({"status": "R ", "path": "new.py", "source": "old.py"}, entries)
            self.assertEqual(sorted(fixcheck.changed_files(repo)), ["a.py", "caf\u00e9.py", "my new.py", "new.py", "old.py"])

    def test_a_rename_in_the_work_tree_column_has_its_source(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            repo = Path(tmp)
            (repo / "old.py").write_text("y = 1\ny = 2\ny = 3\n")
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            (repo / "old.py").rename(repo / "new.py")
            git(repo, "add", "-N", "new.py")
            self.assertEqual(git_status(repo), [{"status": " R", "path": "new.py", "source": "old.py"}])
            self.assertEqual(sorted(fixcheck.changed_files(repo)), ["new.py", "old.py"])

    @unittest.skipIf(sys.platform == "win32", "Windows has no file name with a carriage return")
    def test_a_name_with_a_carriage_return_is_the_real_name(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            repo = Path(tmp)
            (repo / "a\rb.py").write_text("def f():\n    return 1\n")
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            (repo / "a\rb.py").write_text("def f():\n    return 2\n")
            (repo / "c\rd.py").write_text("x = 1\n")
            self.assertEqual(sorted(e["path"] for e in git_status(repo)), ["a\rb.py", "c\rd.py"])
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "b")
            self.assertEqual([f["new"] for f in commands.changed_files(repo, "HEAD~1", "HEAD", ["."])], ["a\rb.py", "c\rd.py"])

    def test_a_file_from_git_keeps_its_carriage_returns(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            repo = Path(tmp)
            (repo / ".gitattributes").write_bytes(b"* -text\n")
            (repo / "m.py").write_bytes(b"def f():\r\n    return 'a\\rb'\r\n")
            git(repo, "init", "-q", "-b", "main")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "a")
            self.assertEqual(common_git(repo, "show", "HEAD:m.py"), (0, "def f():\r\n    return 'a\\rb'\r\n"))

    def test_a_folder_that_is_not_a_repository_gives_none(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            self.assertIsNone(git_status(Path(tmp) / "absent"))


class ScopeCheckTest(unittest.TestCase):
    def test_no_git_status_is_not_a_pass_of_the_scope_check(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            tree, info = Path(tmp) / "tree", Path(tmp) / "info"
            (tree / "tests").mkdir(parents=True)
            info.mkdir()
            (tree / "tests" / "test_new.py").write_text("import unittest\n")
            (info / "spec.json").write_text(json.dumps({"file": "mod.py", "test_file": "tests/test_new.py",
                                                        "python": sys.executable, "scope": ["mod.py"],
                                                        "test_cmd": "{python} -m unittest {tests}", "bugs": []}))
            # `tree` is not a git repository. A parent of the temporary folder must not be one for this test.
            self.assertIsNone(fixcheck.out_of_scope(tree, ["mod.py"]))
            result = fixcheck.check(info, tree)
            self.assertEqual(result["verdict"], "reject")
            self.assertIn("git status failed", "\n".join(result["problems"]))


class SnippetPathTest(unittest.TestCase):
    def test_a_relative_tree_and_a_relative_snippet_run(self):
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            root = Path(tmp)
            (root / "tree" / "src" / "pkg").mkdir(parents=True)
            (root / "tree" / "src" / "pkg" / "__init__.py").write_text("def add(a, b):\n    return a + b\n")
            (root / "info").mkdir()
            (root / "info" / "r.py").write_text("from pkg import add\n\n\ndef run():\n    return add(1, 2)\n")
            before = os.getcwd()
            os.chdir(root)
            try:
                got = run_snippet(Path("tree"), Path("info") / "r.py", root / "home", import_root="src")
            finally:
                os.chdir(before)
            self.assertEqual((got.get("ok"), got.get("result")), (True, "3"), got)


class FunctionsOfTest(unittest.TestCase):
    def test_a_definition_in_a_block_statement_is_a_function_of_the_module(self):
        src = ("import sys\n\nif sys.platform == 'win32':\n    def helper():\n        return 1\nelse:\n    def helper():\n        return 2\n\n"
               "try:\n    import fast\nexcept ImportError:\n    def fast():\n        return 3\nfinally:\n    def last():\n        return 4\n\n"
               "with open(__file__) as h:\n    def inside():\n        return 5\n\n"
               "for k in range(1):\n    def loop():\n        return 6\n\n"
               "class C:\n    if True:\n        def m(self):\n            return 7\n\n"
               "def outer():\n    def inner():\n        return 8\n    return inner\n")
        got = [(f["function"], f["nth"], f["of"], f["start"]) for f in commands.functions_of(src)]
        self.assertEqual(got, [("helper", 1, 2, 4), ("helper", 2, 2, 7), ("fast", 1, 1, 13), ("last", 1, 1, 16),
                               ("inside", 1, 1, 20), ("loop", 1, 1, 24), ("C.m", 1, 1, 29), ("outer", 1, 1, 32)])

    @unittest.skipIf(sys.version_info < (3, 10), "the match statement is new in Python 3.10")
    def test_a_definition_in_a_case_of_a_match_statement(self):
        src = "import sys\n\nmatch sys.platform:\n    case 'win32':\n        def f():\n            return 1\n    case _:\n        def f():\n            return 2\n"
        self.assertEqual([(f["function"], f["nth"]) for f in commands.functions_of(src)], [("f", 1), ("f", 2)])


class SlugTest(unittest.TestCase):
    def test_a_slug_is_never_empty(self):
        for file in ("_.py", "__.py", "pkg/_.py", ".py", "-.py"):
            self.assertRegex(commands.slug_of(file), r"^[a-z0-9-]+-[0-9a-f]{8}$|^[a-z0-9]+(-[a-z0-9]+)*$", file)
            self.assertTrue(commands.slug_of(file).strip("-"), file)
        self.assertNotEqual(commands.slug_of("_.py"), commands.slug_of("__.py"))
        self.assertEqual(commands.slug_of("pkg/mod.py"), "pkg-mod")


class ModuleNameTest(unittest.TestCase):
    def test_the_module_of_an_init_file_is_its_package(self):
        self.assertEqual(fixcheck.module_name("pkg/mod.py"), "mod")
        self.assertEqual(fixcheck.module_name("src/pkg/__init__.py"), "pkg")
        self.assertEqual(fixcheck.module_name("__init__.py"), "")

    def test_a_test_that_imports_the_package_is_related_to_its_init_file(self):
        ok = "import unittest\nimport pkg\n\n\nclass T(unittest.TestCase):\n    def test_v(self):\n        self.assertEqual(pkg.V, 1)\n"
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            tree, info = Path(tmp) / "tree", Path(tmp) / "info"
            (tree / "pkg").mkdir(parents=True)
            (tree / "tests").mkdir()
            info.mkdir()
            (tree / "pkg" / "__init__.py").write_text("V = 1\n")
            (tree / "tests" / "test_new.py").write_text(ok)
            (tree / "tests" / "test_api.py").write_text(ok.replace("pkg.V, 1", "pkg.V, 2000"))
            (info / "spec.json").write_text(json.dumps({"file": "pkg/__init__.py", "test_file": "tests/test_new.py",
                                                        "python": sys.executable,
                                                        "test_cmd": "{python} -m unittest {tests}", "bugs": []}))
            result = fixcheck.check(info, tree)
            self.assertEqual(result["verdict"], "reject")
            self.assertIn("tests of the repository fail", "\n".join(result["problems"]))


class RelatedTestsTest(unittest.TestCase):
    def test_each_related_test_file_runs(self):
        ok = ("import unittest\nfrom pkg.mod import add\n\n\nclass T(unittest.TestCase):\n"
              "    def test_add(self):\n        self.assertEqual(add(1, 2), 3)\n")
        with tempfile.TemporaryDirectory(prefix="hpflow-") as tmp:
            tree, info = Path(tmp) / "tree", Path(tmp) / "info"
            (tree / "pkg").mkdir(parents=True)
            (tree / "tests").mkdir()
            info.mkdir()
            (tree / "pkg" / "__init__.py").write_text("")
            (tree / "pkg" / "mod.py").write_text("def add(a, b):\n    return a + b\n")
            (tree / "tests" / "test_new.py").write_text(ok)
            count = 2 * fixcheck.RELATED_PART + 2
            for k in range(count):
                (tree / "tests" / f"test_mod_{k:02d}.py").write_text(ok)
            (info / "spec.json").write_text(json.dumps({"file": "pkg/mod.py", "test_file": "tests/test_new.py",
                                                        "python": sys.executable,
                                                        "test_cmd": "{python} -m unittest {tests}", "bugs": []}))
            self.assertEqual(fixcheck.check(info, tree)["verdict"], "accept")
            # The last related file in the sort order fails. A limit on the number of files would not run it.
            # Its size is not the size of the first form: Python reuses the bytecode of a source with the same size
            # and the same second of change.
            (tree / "tests" / f"test_mod_{count - 1:02d}.py").write_text(ok.replace("add(1, 2), 3", "add(1, 2), 40000"))
            result = fixcheck.check(info, tree)
            self.assertEqual(result["verdict"], "reject")
            self.assertIn("tests of the repository fail", "\n".join(result["problems"]))


class RepoPathTest(unittest.TestCase):
    def test_each_form_of_one_path_is_one_path(self):
        for text in ("pkg", "./pkg", "pkg/", "./pkg/", "a/../pkg", "pkg/."):
            self.assertEqual(commands.repo_path(text, "--paths"), "pkg", text)
        self.assertEqual(commands.repo_path("src\\pkg", "--paths"), "src/pkg")
        self.assertEqual(commands.repo_path(".", "--import-root"), "")
        self.assertEqual(commands.repo_path("./", "--import-root"), "")

    def test_a_path_outside_the_repository_is_a_usage_error(self):
        for text in ("../pkg", "/abs/pkg", "a/../../pkg", "C:/x", ".."):
            with self.assertRaises(UsageError, msg=text):
                commands.repo_path(text, "--paths")


class LeanConfigTest(unittest.TestCase):
    def test_brackets_in_strings_and_comments_are_not_structure(self):
        cfg = """model = "x"
notify = ["a", "b[c"]
arr = [
  [1, 2],
  ["]", "#"],
]
[mcp_servers.one]
command = "run[this"
args = ["a[b", "c"]  # [not a table]
env = { K = "v]" }
lit = 'it[s'
[profiles.p]
model = "y"
[[plugins]]
x = 1
[model_providers.z]
name = "z"
"""
        self.assertEqual(lean_config(cfg), """model = "x"
arr = [
  [1, 2],
  ["]", "#"],
]
[profiles.p]
model = "y"
[model_providers.z]
name = "z"
""")

    def test_a_table_header_inside_a_multi_line_string_is_text(self):
        cfg = 'note = """a [ b\n[mcp_servers.fake]\n"""\nkeep = 1\n[hooks]\nx = """\n[profiles.q]\n"""\n[profiles.p]\ny = 2\n'
        self.assertEqual(lean_config(cfg), 'note = """a [ b\n[mcp_servers.fake]\n"""\nkeep = 1\n[profiles.p]\ny = 2\n')

    def test_a_multi_line_value_of_a_dropped_top_key_is_dropped_whole(self):
        cfg = 'notify = [\n  "prog",\n  ["x", "y"],\n]\nmodel = "m"\n[t]\nnotify = ["kept: a key of a table"]\n'
        self.assertEqual(lean_config(cfg), 'model = "m"\n[t]\nnotify = ["kept: a key of a table"]\n')

    def test_a_multi_line_string_can_end_with_one_or_two_quote_characters(self):
        for q in ('"', "'"):
            for extra in (0, 1, 2):
                line = f"a = [{q * 3}x{q * (3 + extra)}]"
                self.assertEqual(toml_scan(line, 0, None), (0, None), line)
                self.assertEqual(toml_scan(f"x{q * (3 + extra)}]", 1, q * 3), (0, None), line)
            cfg = f'a = [{q * 3}x{q * 4}]\n[mcp_servers.one]\ncommand = "c"\n[profiles.p]\ny = 2\n'
            self.assertEqual(lean_config(cfg), f'a = [{q * 3}x{q * 4}]\n[profiles.p]\ny = 2\n')

    def test_a_dropped_table_goes_in_each_form(self):
        keep = 'model = "m"\n[profiles.p]\ny = 2\n'
        for form in ('mcp_servers = { one = { command = "c" } }\n',
                     'mcp_servers.one.command = "c"\n',
                     '"mcp_servers".one.command = "c"\n',
                     "'hooks' = { a = 1 }\n",
                     'mcp_servers = {\n  one = { command = "c" },\n}\n',
                     '"notify" = ["prog"]\n',
                     "'notify' = [\n  \"prog\",\n]\n",
                     ' \t"notify" = ["prog"]\n'):
            self.assertEqual(lean_config('model = "m"\n' + form + "[profiles.p]\ny = 2\n"), keep, form)
        for header in ('["mcp_servers".one]', "['mcp_servers'.one]", "[ mcp_servers . one ]", "[[hooks]]", '[["hooks"]]',
                       "[mcp_servers]", '["mcp\\u005fservers"]'):
            cfg = f'model = "m"\n{header}\ncommand = "c"\n[profiles.p]\ny = 2\n'
            self.assertEqual(lean_config(cfg), keep, header)

    def test_another_table_or_key_with_a_name_that_starts_the_same_stays(self):
        for cfg in ('[mcp_servers-old]\ncommand = "c"\n', "[hooks_2]\na = 1\n", '["mcp_servers x"]\na = 1\n',
                    "notify-all = 1\n", "notifyx = 1\n", "[a]\nmcp_servers = 1\nnotify = 2\n",
                    'x = [\n  ["mcp_servers"],\n  ["hooks", "y"],\n]\n[profiles.p]\ny = 2\n'):
            self.assertEqual(lean_config(cfg), cfg, cfg)

    def test_the_first_part_of_a_key(self):
        for text, key in (("a = 1", "a"), ("a.b = 1", "a"), ('"a b".c = 1', "a b"), ("'a'.b = 1", "a"), ("  a-b_1 = 1", "a-b_1"),
                          ("# a comment", None), ("", None), ("= 1", None), ('"open', None), ("'open", None)):
            self.assertEqual(first_key(text), key, text)

    def test_an_escaped_quote_does_not_close_a_basic_multi_line_string(self):
        self.assertEqual(toml_scan('a\\"""b', 0, '"""'), (0, '"""'))
        self.assertEqual(toml_scan('a\\\\"""] [', 1, '"""'), (1, None))
        # A literal multi-line string has no escape.
        self.assertEqual(toml_scan("a\\'''] [", 1, "'''"), (1, None))

    def test_the_scanner_reads_escapes(self):
        self.assertEqual(toml_scan('s = "a\\" [', 0, None), (0, None))
        self.assertEqual(toml_scan('s = "a\\\\" [', 0, None), (1, None))
        self.assertEqual(toml_scan('s = """a', 0, None), (0, '"""'))
        self.assertEqual(toml_scan('b""" [', 0, '"""'), (1, None))


class ImportsModuleTest(unittest.TestCase):
    def test_each_import_form_names_the_module(self):
        for source in ("import mod", "import pkg.mod", "import pkg.mod as m", "from pkg.mod import f", "from mod import f",
                       "from pkg import a, mod", "from pkg import (\n    a,\n    mod,\n)", "from pkg import mod as m",
                       "def t():\n    from pkg import mod\n", "from . import mod", "from .mod import f"):
            self.assertTrue(imports_module(source, "mod"), source)

    def test_another_module_is_not_the_module(self):
        for source in ("import model", "from pkg.models import mod_x", "from pkg import mode", "x = 'import mod'",
                       "# import mod", "import pkg.modx", "def broken(:\n    import mod"):
            self.assertFalse(imports_module(source, "mod"), source)


if __name__ == "__main__":
    unittest.main()
