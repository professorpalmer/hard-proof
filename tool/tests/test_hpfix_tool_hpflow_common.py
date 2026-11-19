"""Regression tests of shell_quote and run_group in hpflow.common."""
from __future__ import annotations

import os
import sys
import time
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow import common  # noqa: E402
from hpflow.common import run_group, shell_quote  # noqa: E402


class WindowsQuoteTest(unittest.TestCase):
    def setUp(self):
        self.old = common.WINDOWS
        common.WINDOWS = True

    def tearDown(self):
        common.WINDOWS = self.old

    def test_cmd_metacharacters_are_quoted(self):
        self.assertEqual(shell_quote("a&calc"), '"a&calc"')
        self.assertEqual(shell_quote(r"C:\R&D\out"), r'"C:\R&D\out"')
        self.assertEqual(shell_quote("a|b"), '"a|b"')

    def test_a_trailing_backslash_doubles_inside_quotes(self):
        self.assertEqual(shell_quote("C:\\R&D\\"), '"C:\\R&D\\\\"')

    def test_plain_and_spaced_arguments_keep_their_form(self):
        self.assertEqual(shell_quote(r"C:\Python\python.exe"), r"C:\Python\python.exe")
        self.assertEqual(shell_quote(r"C:\Program Files\a&b"), r'"C:\Program Files\a&b"')


class PosixQuoteTest(unittest.TestCase):
    def test_posix_quote_is_unchanged(self):
        old = common.WINDOWS
        common.WINDOWS = False
        try:
            self.assertEqual(shell_quote("a&calc"), "'a&calc'")
            self.assertEqual(shell_quote("plain"), "plain")
        finally:
            common.WINDOWS = old


@unittest.skipIf(os.name == "nt", "the test command uses POSIX sh")
class BackgroundChildTest(unittest.TestCase):
    def test_a_background_child_does_not_hold_the_result(self):
        start = time.monotonic()
        result = run_group("sleep 30 & echo done", shell=True, timeout=10)
        self.assertEqual(result, (0, "done\n", ""))
        self.assertLess(time.monotonic() - start, 8)

    def test_a_command_that_runs_too_long_still_times_out(self):
        code, out, _ = run_group("echo start; sleep 30", shell=True, timeout=1)
        self.assertIsNone(code)
        self.assertEqual(out, "start\n")

    def test_exit_code_output_and_input_stay(self):
        self.assertEqual(run_group("cat; echo err >&2; exit 3", shell=True, timeout=10, stdin="hi\n"),
                         (3, "hi\n", "err\n"))
        big = "x" * 1_000_000
        code, out, _ = run_group([sys.executable, "-c", "import sys; sys.stdout.write(sys.stdin.read())"],
                                 timeout=30, stdin=big)
        self.assertEqual((code, len(out)), (0, len(big)))


if __name__ == "__main__":
    unittest.main()
