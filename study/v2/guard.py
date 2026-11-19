#!/usr/bin/env python3
"""Hard Proof v2: load limits for this machine (48 GB of memory).

On 2026-11-18 the machine ran out of memory two times in four minutes and restarted:
one extra Lean kernel (`con-leche`) used 77 GB on one proof, and then 120 `node` processes
from test runs in eight worktrees used 93 GB. These limits are the answer.

    slot()            at most MAX_WORKERS agent workers at one time, for all scripts together
    locked(name)      one holder at a time for a named resource (for example a test run)
    wait_for_memory() block while free memory is below MIN_FREE_PERCENT

Command line:
    python3 guard.py run-locked NAME -- command ...     run a command with the named lock held
    python3 guard.py status
"""
from __future__ import annotations

import contextlib
import fcntl
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path.home() / "Projects" / "hp-work" / "guard"
MAX_WORKERS = int(os.environ.get("HP_MAX_WORKERS", "5"))
MIN_FREE_PERCENT = int(os.environ.get("HP_MIN_FREE_PERCENT", "30"))


def free_percent() -> int:
    try:
        out = subprocess.run(["memory_pressure"], capture_output=True, text=True, timeout=20).stdout
        for line in out.splitlines():
            if "free percentage" in line:
                return int(line.rsplit(":", 1)[1].strip().rstrip("%"))
    except Exception:
        pass
    return 100


def wait_for_memory(need: int = MIN_FREE_PERCENT, poll: float = 15.0) -> None:
    while free_percent() < need:
        time.sleep(poll)


@contextlib.contextmanager
def locked(name: str):
    ROOT.mkdir(parents=True, exist_ok=True)
    fh = open(ROOT / f"{name}.lock", "w")
    try:
        fcntl.flock(fh, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(fh, fcntl.LOCK_UN)
        fh.close()


@contextlib.contextmanager
def slot():
    """Hold one of MAX_WORKERS worker slots. Blocks until a slot is free and memory is sufficient."""
    ROOT.mkdir(parents=True, exist_ok=True)
    held = None
    while held is None:
        for i in range(MAX_WORKERS):
            fh = open(ROOT / f"slot{i}.lock", "w")
            try:
                fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
                held = fh
                break
            except OSError:
                fh.close()
        if held is None:
            time.sleep(3)
    try:
        wait_for_memory()
        yield
    finally:
        fcntl.flock(held, fcntl.LOCK_UN)
        held.close()


def main() -> int:
    args = sys.argv[1:]
    if args[:1] == ["status"]:
        busy = 0
        ROOT.mkdir(parents=True, exist_ok=True)
        for i in range(MAX_WORKERS):
            fh = open(ROOT / f"slot{i}.lock", "w")
            try:
                fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
                fcntl.flock(fh, fcntl.LOCK_UN)
            except OSError:
                busy += 1
            fh.close()
        print(f"free memory {free_percent()}%, worker slots in use {busy} of {MAX_WORKERS}")
        return 0
    if len(args) >= 4 and args[0] == "run-locked" and args[2] == "--":
        with locked(args[1]):
            wait_for_memory(20)
            return subprocess.run(args[3:]).returncode
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
