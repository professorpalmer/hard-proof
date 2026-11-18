"""The README quick start, step by step, in a fresh copy of `examples/clamp`.

The copy has no build cache and no run log. The steps use the `hp` launcher
with the current folder as the domain folder.
"""
from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from helpers import EXAMPLES, TOOL

STEPS = [
    (["check", "model"], "accept"),
    (["link", "--repo", "pycode", "--cases", "5000"], "agree"),
    (["check", "laws", "ref"], "accept"),
    (["pin"], "accept"),
    (["verify-pins"], "accept"),
    (["status"], "accept"),
]


class QuickStartTest(unittest.TestCase):
    def test_quick_start(self):
        with tempfile.TemporaryDirectory(prefix="hardproof-quickstart-") as tmp:
            demo = Path(tmp) / "clamp-demo"
            shutil.copytree(EXAMPLES / "clamp", demo,
                            ignore=shutil.ignore_patterns(".lake", "hardproof_runs.jsonl", "__pycache__"))
            self.assertFalse((demo / "hp" / ".lake").exists())
            for args, verdict in STEPS:
                proc = subprocess.run([str(TOOL / "hp"), *args], cwd=str(demo), capture_output=True,
                                      text=True, timeout=900)
                report = json.loads(proc.stdout)
                self.assertEqual(report["verdict"], verdict, f"{args}: {proc.stdout[-2000:]}{proc.stderr[-2000:]}")
                self.assertEqual(proc.returncode, 0, args)
            self.assertTrue((demo / "hardproof.lock.json").exists())
            # Two checks and one link test write to the run log.
            self.assertEqual(len((demo / "hardproof_runs.jsonl").read_text().splitlines()), 3)


if __name__ == "__main__":
    unittest.main()
