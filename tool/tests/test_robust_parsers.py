"""Tests of the three readers that take text from outside hpflow: git names, the Codex config, test imports.

Each one had a parser of our own that failed on a new input form in each audit. Each now uses a form that has
no such cases: the NUL-separated name list of git, a scanner that knows TOML strings, and the Python parser.
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from hpflow import commands  # noqa: E402
from hpflow.codexhome import lean_config, toml_scan  # noqa: E402
from hpflow.common import UsageError  # noqa: E402
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
