"""Regression tests of the checks of --passes, --group-size and the package folder of init. No model call."""
from __future__ import annotations

import subprocess
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow import cli  # noqa: E402
from hpflow import commands as c  # noqa: E402
from hpflow.common import UsageError  # noqa: E402


def review_parser() -> cli.Parser:
    p = cli.Parser(prog="x")
    cli.add_review(p)
    return p


class PassesOptionTest(unittest.TestCase):
    def test_passes_zero_or_less_is_a_usage_error(self):
        for value in ("0", "-1"):
            with self.assertRaises(UsageError):
                review_parser().parse_args(["--passes", value])

    def test_passes_one_and_two_are_kept(self):
        self.assertEqual(review_parser().parse_args([]).passes, 1)
        self.assertEqual(review_parser().parse_args(["--passes", "2"]).passes, 2)

    def test_audit_parser_rejects_passes_zero(self):
        with self.assertRaises(UsageError):
            cli.build_parser().parse_args(["audit", "--out", "o", "--repo", "r", "--ref", "x",
                                           "--changed", "a..b", "--passes", "0"])


class GroupSizeOptionTest(unittest.TestCase):
    def test_group_size_zero_or_less_is_a_usage_error(self):
        for value in ("0", "-3"):
            with self.assertRaises(UsageError):
                review_parser().parse_args(["--group", "file", "--group-size", value])

    def test_group_size_one_and_default_are_kept(self):
        self.assertEqual(review_parser().parse_args([]).group_size, 6)
        self.assertEqual(review_parser().parse_args(["--group", "file", "--group-size", "1"]).group_size, 1)

    def test_a_word_is_still_a_usage_error(self):
        with self.assertRaises(UsageError):
            review_parser().parse_args(["--group-size", "many"])


def audit_args(passes: int) -> types.SimpleNamespace:
    return types.SimpleNamespace(
        command="audit", adapter=None, agent_cmd=None, model=None, models=None,
        shell=True, repo="r", ref="x", paths=None, python=None, test_cmd=None, import_root=None,
        changed="a..b", functions=None, files=None, max_lines=150, max_n=None, passes=passes,
        repro_timeout=60, group="function", group_size=6, short_prompt=False, staged=True,
        findings=None, source=None)


class AuditPassesTest(unittest.TestCase):
    def run_audit(self, passes: int):
        seen = {}

        def rev(ctx, model, shell, n, *a):
            seen["passes"] = n
            return {"ok": True}
        ok = lambda *a: {"ok": True}  # noqa: E731
        with tempfile.TemporaryDirectory() as d, \
                mock.patch.object(c, "cmd_init", ok), mock.patch.object(c, "cmd_targets", ok), \
                mock.patch.object(c, "cmd_review", rev), mock.patch.object(c, "cmd_verify", ok):
            ctx = types.SimpleNamespace(out=Path(d), lean=True)
            return cli.run_command(audit_args(passes), ctx), seen

    def test_audit_with_passes_zero_is_a_usage_error_before_init(self):
        with self.assertRaises(UsageError) as e:
            self.run_audit(0)
        self.assertIn("--passes must be 1 or more", str(e.exception))

    def test_audit_with_one_pass_runs(self):
        r, seen = self.run_audit(1)
        self.assertEqual((r["ok"], seen), (True, {"passes": 1}))


class InitPackageFolderTest(unittest.TestCase):
    def make_repo(self, root: Path, package: bool) -> Path:
        repo = root / "repo"
        repo.mkdir()
        (repo / "README.md").write_text("hi\n")
        if package:
            (repo / "pkg").mkdir()
            (repo / "pkg" / "__init__.py").write_text("")

        def g(*a: str) -> None:
            subprocess.run(["git", "-C", str(repo), "-c", "user.name=a", "-c", "user.email=a@b.c", *a],
                           capture_output=True, check=True)
        g("init", "-q")
        g("add", ".")
        g("commit", "-qm", "x")
        return repo

    def test_no_package_but_a_readme_is_a_usage_error(self):
        with tempfile.TemporaryDirectory() as t:
            repo = self.make_repo(Path(t), package=False)
            with self.assertRaises(UsageError) as e:
                c.cmd_init(c.Context(Path(t) / "out", None), str(repo), "HEAD", None, None, None)
            self.assertIn("no package folder", str(e.exception))

    def test_a_package_keeps_the_extra_paths(self):
        with tempfile.TemporaryDirectory() as t:
            repo = self.make_repo(Path(t), package=True)
            r = c.cmd_init(c.Context(Path(t) / "out", None), str(repo), "HEAD", None, None, None)
            self.assertEqual(r["audit"]["paths"], ["pkg", "README.md"])


if __name__ == "__main__":
    unittest.main()
