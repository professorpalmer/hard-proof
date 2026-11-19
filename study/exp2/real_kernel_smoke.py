#!/usr/bin/env python3
"""Hard Proof, experiment 2: a check of the simulated parts against the real kernel.

A real child process takes the real lock. The parent reads the lock file and
compares the stored identity with the kernel answer. The parent then kills the
child and takes the lock. No part is simulated. The kernel does not let a test
force pid reuse, so this check does not cover it.
"""
from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

PM = Path.home() / "Projects" / "Puppetmaster"
sys.path.insert(0, str(PM))
from puppetmaster.interprocess_lock import InterProcessFileLock  # noqa: E402
from puppetmaster.proc_identity import process_identity  # noqa: E402

CHILD = (
    "import sys, time; sys.path.insert(0, sys.argv[1]);"
    "from pathlib import Path;"
    "from puppetmaster.interprocess_lock import InterProcessFileLock;"
    "InterProcessFileLock(Path(sys.argv[2]), timeout=5).acquire();"
    "print('held', flush=True); time.sleep(600)"
)


def main() -> int:
    work = Path(tempfile.mkdtemp(prefix="hardproof-kernel-"))
    target = work / "target.json"
    child = subprocess.Popen([sys.executable, "-c", CHILD, str(PM), str(target)],
                             stdout=subprocess.PIPE, text=True)
    assert child.stdout.readline().strip() == "held"
    record = json.loads((work / ".target.json.lock").read_text())
    kernel = process_identity(child.pid)
    out = {
        "own_identity_readable": process_identity(os.getpid()) is not None,
        "record_pid_is_child": record["pid"] == child.pid,
        "record_identity_equals_kernel_answer": record["proc"] is not None and record["proc"] == kernel,
    }
    try:
        InterProcessFileLock(target, timeout=0.3).acquire()
        out["live_owner_refuses"] = False
    except TimeoutError:
        out["live_owner_refuses"] = True
    child.send_signal(signal.SIGKILL)
    child.wait()
    time.sleep(0.1)
    lock = InterProcessFileLock(target, timeout=1.0)
    try:
        lock.acquire()
        out["dead_owner_grants"] = True
        lock.release()
    except TimeoutError:
        out["dead_owner_grants"] = False
    out["identity_of_dead_pid_is_none"] = process_identity(child.pid) is None
    print(json.dumps(out, indent=2))
    return 0 if all(out.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
