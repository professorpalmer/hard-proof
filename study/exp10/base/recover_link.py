#!/usr/bin/env python3
"""Hard Proof, experiment 10: the link between `Recover.ref` and the shipped code.

Each case of a full grid goes to two systems:

1. `Recover.ref`, the Lean mirror of the code.
2. The real `InterProcessFileLock._recover_stale_owner` on a real lock file.

The two must agree on "remove the lock file" for each case.

Replaced parts (assumptions of the link):
  - `interprocess_lock._pid_is_alive`   the kernel answer "is this pid alive"
  - `interprocess_lock.pid_reused`      the kernel answer "is this a later process"
  - `time.time`                         a fixed clock, so the age is exact
  - `Path.stat` fails for the cases with an unknown age

Usage:
    python3 recover_link.py [--pm PATH] [--mutant NAME]

Mutants: `ignore-reuse` (pid_reused always answers False),
         `always-alive` (the liveness probe always answers True).
"""
from __future__ import annotations

import argparse
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
NOW = 1_000_000.0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pm", type=Path, default=Path.home() / "Projects" / "Puppetmaster")
    parser.add_argument("--mutant", choices=["ignore-reuse", "always-alive"], default=None)
    args = parser.parse_args()
    started = time.time()
    sys.path.insert(0, str(args.pm))
    import puppetmaster
    from puppetmaster import interprocess_lock as il

    grid = list(itertools.product([0, 1], [0, 1], [0, 1], [None, 0, 9, 10, 11, 500], [0, 10, 120]))
    text = "".join(f"{k} {a} {r} {'-' if age is None else age} {st}\n" for k, a, r, age, st in grid)
    proc = subprocess.run(["lake", "env", "lean", "--run", "RecoverRunner.lean"], cwd=HERE,
                          input=text, capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit("model runner failed:\n" + proc.stderr[-2000:])
    model = [line == "1" for line in proc.stdout.split("\n")[: len(grid)]]

    differ = []
    scratch = Path(tempfile.mkdtemp(prefix="hardproof-recover-"))
    try:
        for index, (case, want) in enumerate(zip(grid, model)):
            known, alive, reused, age, stale = case
            work = scratch / f"c{index}"
            work.mkdir()
            lock = il.InterProcessFileLock(work / "target.json", timeout=0.0, stale_after=float(stale))
            record = {"pid": 4242 if known else "not-a-pid", "token": "t", "proc": "recorded"}
            if age is not None:
                record["created_at"] = NOW - age
            lock.path.write_text(json.dumps(record), encoding="utf-8")
            patches = [
                mock.patch.object(il, "_pid_is_alive", lambda pid: True if args.mutant == "always-alive" else bool(alive)),
                mock.patch.object(il, "pid_reused", lambda pid, rec: False if args.mutant == "ignore-reuse" else bool(reused)),
                mock.patch("time.time", return_value=NOW),
            ]
            if age is None:
                patches.append(mock.patch.object(type(lock.path), "stat", side_effect=OSError("no stat")))
            for p in patches:
                p.start()
            try:
                removed = lock._recover_stale_owner()
            finally:
                for p in reversed(patches):
                    p.stop()
            gone = not lock.path.exists()
            if removed != want or gone != want:
                differ.append({"case": dict(zip(["pidKnown", "alive", "reused", "age", "staleAfter"], case)),
                               "model": want, "code_returned": removed, "file_removed": gone})
    finally:
        shutil.rmtree(scratch, ignore_errors=True)

    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=args.pm,
                            capture_output=True, text=True).stdout.strip()
    report = {
        "experiment": "exp10-link-stale-lock-recovery", "mutant": args.mutant,
        "verdict": "agree" if not differ else "disagree",
        "code": {"function": "InterProcessFileLock._recover_stale_owner",
                 "version": getattr(puppetmaster, "__version__", "unknown"), "commit": commit},
        "cases": len(grid), "grid": "pidKnown x alive x reused x age {unknown,0,9,10,11,500} x stale_after {0,10,120}",
        "cases_that_differ": len(differ), "first_difference": differ[0] if differ else None,
        "seconds": round(time.time() - started, 2),
    }
    print(json.dumps(report, indent=2))
    return 0 if not differ else 1


if __name__ == "__main__":
    sys.exit(main())
