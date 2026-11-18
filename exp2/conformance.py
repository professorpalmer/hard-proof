#!/usr/bin/env python3
"""Hard Proof, experiment 2: the link between the proved model and real code.

The test sends the same event traces to two systems:

1. The Lean model from experiment 1 (`Laws.step` with the proved `Exp.lock`).
2. The real `puppetmaster.interprocess_lock.InterProcessFileLock`, on a real
   lock file, with a simulated operating system below it.

After each event the two observations must agree: the owner record and the set
of processes in the critical section. The test also checks Law 1 and Law 2
directly on the real code.

Simulated parts (these are assumptions of the link, not tested facts):
  - `os.getpid`                          the pid of the simulated process
  - `proc_identity.process_identity`     the kernel start token for a pid
  - `interprocess_lock._pid_is_alive`    the kernel answer "is this pid alive"

Modes:
  base           the real code, as it is
  no-identity    the platform gives no start token (`process_identity` is None)
  ignore-reuse   `pid_reused` always answers False (the behavior before 1.29.0)

Usage:
    python3 conformance.py [--mode MODE] [--traces N] [--length N] [--seed N]

Exit code: 0 when the code agrees with the model and obeys the laws, else 1.
"""
from __future__ import annotations

import argparse
import json
import random
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Optional
from unittest import mock

HERE = Path(__file__).resolve().parent
EXP1 = HERE.parent / "exp1"

DIRECTED = [
    # The trace that kills the pid-only mutant, then a request from a new process.
    ["spawn 5", "acquire 5", "exit 5", "spawn 5", "spawn 6", "acquire 6"],
    # The new process with the old pid makes the request.
    ["spawn 5", "acquire 5", "exit 5", "spawn 5", "acquire 5"],
    # A live owner keeps the lock.
    ["spawn 1", "spawn 2", "acquire 1", "acquire 2", "release 1", "acquire 2"],
    # A process that is not the owner cannot release.
    ["spawn 1", "spawn 2", "acquire 1", "release 2", "acquire 2"],
    # A dead owner with a free pid gives the lock to the next request.
    ["spawn 1", "spawn 2", "acquire 1", "exit 1", "acquire 2"],
]


def random_trace(rng: random.Random, length: int, pids: int) -> list[str]:
    kinds = ["spawn"] * 6 + ["exit"] * 4 + ["acquire"] * 7 + ["release"] * 3
    return [f"{rng.choice(kinds)} {rng.randint(1, pids)}" for _ in range(length)]


def run_model(traces: list[list[str]]) -> list[list[str]]:
    text = "\n".join("\n".join(t) + "\nreset" for t in traces) + "\n"
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(HERE / "Runner.lean")],
        cwd=EXP1, input=text, capture_output=True, text=True,
    )
    if proc.returncode != 0:
        raise SystemExit("model runner failed:\n" + proc.stderr[-2000:])
    out: list[list[str]] = []
    current: list[str] = []
    for line in proc.stdout.splitlines():
        if line == "reset":
            out.append(current)
            current = []
        else:
            current.append(line)
    return out


class SimOS:
    def __init__(self) -> None:
        self.table: dict[int, int] = {}
        self.next = 0


CURRENT: Optional[SimOS] = None
MODE = "base"


def sim_identity(pid: int) -> Optional[str]:
    if MODE == "no-identity":
        return None
    tok = CURRENT.table.get(pid) if CURRENT is not None else None
    return None if tok is None else str(tok)


def sim_alive(pid: int) -> bool:
    return CURRENT is not None and pid in CURRENT.table


class CodeRun:
    """One trace against the real lock, on a new lock file."""

    def __init__(self, lock_cls, proc_identity_mod, workdir: Path, stats: dict) -> None:
        self.lock_cls = lock_cls
        self.pi = proc_identity_mod
        self.target = workdir / "target.json"
        self.lock_file = workdir / ".target.json.lock"
        self.os = SimOS()
        self.procs: list[tuple[int, int]] = []
        self.holders: dict[tuple[int, int], object] = {}
        self.stats = stats
        self.law_problems: list[str] = []

    def owner_record(self) -> Optional[tuple[int, Optional[str]]]:
        try:
            data = json.loads(self.lock_file.read_text(encoding="utf-8"))
        except FileNotFoundError:
            return None
        return data.get("pid"), data.get("proc")

    def render(self) -> str:
        rec = self.owner_record()
        owner = "none" if rec is None else f"{rec[0]}:{'?' if rec[1] is None else rec[1]}"
        inside = [p for p in self.procs if p in self.holders]
        cs = "none" if not inside else ",".join(f"{p}:{t}" for p, t in inside)
        return f"owner={owner} cs={cs}"

    def apply(self, event: str) -> str:
        global CURRENT
        CURRENT = self.os
        kind, raw = event.split()
        pid = int(raw)
        tok = self.os.table.get(pid)
        if kind == "spawn":
            if tok is None:
                self.os.table[pid] = self.os.next
                self.procs.append((pid, self.os.next))
                self.os.next += 1
        elif kind == "exit":
            if tok is not None:
                del self.os.table[pid]
                self.holders.pop((pid, tok), None)  # a crash: no release
        elif kind == "acquire":
            if tok is not None:
                self.acquire(pid, tok)
        elif kind == "release":
            if tok is not None:
                lock = self.holders.pop((pid, tok), None)
                if lock is not None:
                    lock.release()
        if len(self.holders) > 1:
            self.law_problems.append(f"law 1 after '{event}': holders {sorted(self.holders)}")
        return self.render()

    def acquire(self, pid: int, tok: int) -> None:
        rec = self.owner_record()
        if rec is not None and isinstance(rec[0], int):
            now = self.os.table.get(rec[0])
            recorded = rec[1]
            if now is not None and recorded is not None and str(now) != recorded:
                self.stats["requests_with_reused_owner_pid"] += 1
            elif now is None:
                self.stats["requests_with_dead_owner"] += 1
        self.pi._OWN = None  # one interpreter plays each process in turn
        lock = self.lock_cls(self.target, timeout=0.0)
        with mock.patch("os.getpid", return_value=pid):
            try:
                lock.acquire()
                granted = True
            except TimeoutError:
                granted = False
        if granted:
            self.stats["grants"] += 1
            self.holders[(pid, tok)] = lock
        else:
            self.stats["refusals"] += 1
            if not self.holders:
                self.law_problems.append(
                    f"law 2: request from {pid}:{tok} refused, critical section is empty")


def same(model_line: str, code_line: str) -> bool:
    if model_line == code_line:
        return True
    if MODE != "no-identity":
        return False
    # The code stores no token in this mode. Compare the pid of the owner and the set.
    m_owner, m_cs = model_line.split(" ")
    c_owner, c_cs = code_line.split(" ")
    return m_cs == c_cs and m_owner.split(":")[0] == c_owner.split(":")[0]


def main() -> int:
    global MODE
    parser = argparse.ArgumentParser(description="Hard Proof link test, experiment 2")
    parser.add_argument("--mode", choices=["base", "no-identity", "ignore-reuse"], default="base")
    parser.add_argument("--traces", type=int, default=2000)
    parser.add_argument("--length", type=int, default=30)
    parser.add_argument("--pids", type=int, default=3)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--pm", type=Path, default=Path.home() / "Projects" / "Puppetmaster")
    args = parser.parse_args()
    MODE = args.mode
    started = time.time()

    sys.path.insert(0, str(args.pm))
    import puppetmaster
    from puppetmaster import interprocess_lock, proc_identity

    proc_identity.process_identity = sim_identity
    interprocess_lock._pid_is_alive = sim_alive
    if MODE == "ignore-reuse":
        interprocess_lock.pid_reused = lambda pid, recorded: False

    rng = random.Random(args.seed)
    traces = list(DIRECTED) + [random_trace(rng, args.length, args.pids) for _ in range(args.traces)]
    model = run_model(traces)
    if len(model) != len(traces):
        raise SystemExit(f"model gave {len(model)} traces, expected {len(traces)}")

    stats = {"grants": 0, "refusals": 0, "requests_with_dead_owner": 0,
             "requests_with_reused_owner_pid": 0}
    divergent = 0
    first_divergence = None
    law_traces = 0
    first_law_problem = None
    events = 0
    scratch = Path(tempfile.mkdtemp(prefix="hardproof-link-"))
    try:
        for index, trace in enumerate(traces):
            workdir = scratch / f"t{index}"
            workdir.mkdir()
            run = CodeRun(interprocess_lock.InterProcessFileLock, proc_identity, workdir, stats)
            diverged = False
            for step, event in enumerate(trace):
                code_line = run.apply(event)
                events += 1
                if not diverged and not same(model[index][step], code_line):
                    diverged = True
                    divergent += 1
                    if first_divergence is None:
                        first_divergence = {"trace": trace[: step + 1],
                                            "model": model[index][step], "code": code_line}
            if run.law_problems:
                law_traces += 1
                if first_law_problem is None:
                    first_law_problem = {"trace": trace, "problem": run.law_problems[0]}
            shutil.rmtree(workdir, ignore_errors=True)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)

    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=args.pm,
                            capture_output=True, text=True).stdout.strip()
    ok = divergent == 0 and law_traces == 0
    report = {
        "experiment": "exp2-link-interprocess-lock",
        "mode": MODE,
        "verdict": "agree" if ok else "disagree",
        "link_grade": "T",
        "code": {"module": "puppetmaster.interprocess_lock.InterProcessFileLock",
                 "version": getattr(puppetmaster, "__version__", "unknown"), "commit": commit},
        "traces": len(traces), "events": events, "seed": args.seed,
        "trace_length": args.length, "pids": args.pids,
        "divergent_traces": divergent, "first_divergence": first_divergence,
        "traces_with_law_problem": law_traces, "first_law_problem": first_law_problem,
        "coverage": stats,
        "simulated": ["os.getpid", "proc_identity.process_identity",
                      "interprocess_lock._pid_is_alive"],
        "seconds": round(time.time() - started, 2),
    }
    print(json.dumps(report, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
