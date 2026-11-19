"""Shared helpers for the hardproof tests. No test makes a model call."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parent.parent
EXAMPLES = TOOL / "examples"
PUPPETMASTER = Path.home() / "Projects" / "hp-work" / "Puppetmaster"
SKIP = shutil.ignore_patterns("variants", "hardproof_runs.jsonl", "hardproof.lock.json", "__pycache__")


def run_hp(domain: Path, *args: str, timeout: float = 900) -> tuple:
    """Run `python3 -m hpflow.proof --dir DOMAIN ARGS`. Return (exit code, JSON report)."""
    env = dict(os.environ)
    env["PYTHONPATH"] = str(TOOL)
    proc = subprocess.run([sys.executable, "-m", "hpflow.proof", "--dir", str(domain), "--actor", "test", *args],
                          cwd=str(TOOL), capture_output=True, text=True, env=env, timeout=timeout)
    try:
        report = json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(f"no JSON report. stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}")
    return proc.returncode, report


class DomainCase(unittest.TestCase):
    """A test case with a scratch copy of an example domain."""

    example = ""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="hardproof-test-")
        self.dir = Path(self._tmp.name) / self.example
        shutil.copytree(EXAMPLES / self.example, self.dir, ignore=SKIP)

    def tearDown(self):
        self._tmp.cleanup()

    def overlay(self, variant: str) -> None:
        for path in (EXAMPLES / self.example / "variants" / variant).iterdir():
            shutil.copy(path, self.dir / path.name)

    def write(self, name: str, text: str) -> None:
        (self.dir / name).write_text(text, encoding="utf-8")

    def read(self, name: str) -> str:
        return (self.dir / name).read_text(encoding="utf-8")

    def remove(self, *names: str) -> None:
        for name in names:
            path = self.dir / name
            if path.exists():
                path.unlink()

    def hp(self, *args: str) -> tuple:
        return run_hp(self.dir, *args)

    def result(self, report: dict, kind: str) -> dict:
        return next(r for r in report["results"] if r["kind"] == kind)

    def assertAccept(self, code: int, report: dict) -> None:
        self.assertEqual(report["verdict"], "accept", json.dumps(report, indent=1)[-3000:])
        self.assertEqual(code, 0)

    def assertReject(self, code: int, report: dict) -> None:
        self.assertEqual(report["verdict"], "reject", json.dumps(report, indent=1)[-3000:])
        self.assertEqual(code, 1)
