"""Regression tests of the related-test search in hpflow.fixcheck."""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow import fixcheck  # noqa: E402

OK_TEST = ("import unittest\nfrom pkg.mod import add\n\n\nclass T(unittest.TestCase):\n"
           "    def test_add(self):\n        self.assertEqual(add(1, 2), 3)\n")


def make_tree(tmp: Path, other_test: str) -> tuple:
    tree, info = tmp / "tree", tmp / "info"
    (tree / "pkg").mkdir(parents=True)
    (tree / "tests").mkdir()
    info.mkdir()
    (tree / "pkg" / "__init__.py").write_text("")
    (tree / "pkg" / "mod.py").write_text("def add(a, b):\n    return a + b\n")
    (tree / "pkg" / "module.py").write_text("def add(a, b):\n    return a + b\n")
    (tree / "tests" / "test_new.py").write_text(OK_TEST)
    (tree / "tests" / "test_other.py").write_text(other_test)
    (info / "spec.json").write_text(json.dumps({"file": "pkg/mod.py", "test_file": "tests/test_new.py",
                                                "python": sys.executable,
                                                "test_cmd": "{python} -m unittest {tests}", "bugs": []}))
    return info, tree


class RelatedTestSearch(unittest.TestCase):
    def test_a_dotted_import_at_line_end_is_related(self):
        bad = ("import unittest\nimport pkg.mod\n\n\nclass T(unittest.TestCase):\n"
               "    def test_add(self):\n        self.assertEqual(pkg.mod.add(1, 2), 4)\n")
        with tempfile.TemporaryDirectory() as tmp:
            info, tree = make_tree(Path(tmp), bad)
            result = fixcheck.check(info, tree)
        self.assertEqual(result["verdict"], "reject")
        self.assertIn("tests of the repository fail", "\n".join(result["problems"]))

    def test_a_dotted_import_of_another_module_is_not_related(self):
        # The stem `mod` is a prefix of `module`. That test does not name the changed module.
        bad = ("import unittest\nimport pkg.module\n\n\nclass T(unittest.TestCase):\n"
               "    def test_add(self):\n        self.assertEqual(pkg.module.add(1, 2), 4)\n")
        with tempfile.TemporaryDirectory() as tmp:
            info, tree = make_tree(Path(tmp), bad)
            self.assertEqual(fixcheck.check(info, tree)["verdict"], "accept")


if __name__ == "__main__":
    unittest.main()
