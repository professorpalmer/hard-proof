#!/usr/bin/env python3
"""Hard Proof, experiment 6: the gap gate.

The gate accepts an adversary result only when `lake comparator` accepts it:
two lock designs, proofs that each design passes each law, and a proof that
the designs differ on one sequence of events. The gate makes no model call.

After an accept it prints the question for the human: the two designs, step
by step, on the trace.

Usage:
    python3 gap_gate.py check

Exit code: 0 for accept, 1 for reject.
"""
from __future__ import annotations

import json
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RUN_LOG = "gap_runs.jsonl"


def run(cmd: list[str]) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return proc.returncode, (proc.stdout + proc.stderr)


def clean(text: str) -> str:
    keep = [l for l in text.splitlines() if not l.startswith(("trace:", "Exporting"))]
    return "\n".join(keep)[-6000:]


def finish(report: dict, started: float, actor: str) -> int:
    report["seconds"] = round(time.time() - started, 2)
    print(json.dumps(report, indent=2))
    with (ROOT / RUN_LOG).open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "actor": actor,
                             "verdict": report["verdict"], "stage": report["stage"],
                             "seconds": report["seconds"]}) + "\n")
    return 0 if report["verdict"] == "accept" else 1


def main() -> int:
    actor = "agent"
    args = sys.argv[1:]
    if "--actor" in args:
        actor = args[args.index("--actor") + 1]
    if not args or args[0] != "check":
        print(__doc__)
        return 2
    started = time.time()
    report: dict = {"experiment": "exp6-gap", "verdict": "reject", "stage": "", "problems": []}

    if not (ROOT / "GapSolution.lean").exists():
        report.update(stage="absent_file", problems=["GapSolution.lean does not exist"])
        return finish(report, started, actor)

    code, out = run(["lake", "build", "GapSolution"])
    if code != 0:
        report.update(stage="build", problems=["GapSolution.lean does not build"], output=clean(out))
        return finish(report, started, actor)

    cfg = json.loads((ROOT / "comparator_gap.json").read_text(encoding="utf-8"))
    names = cfg["theorem_names"] + cfg["definition_names"]
    probe = ROOT / ".lake" / "gap_names.lean"
    probe.write_text("import GapSolution\n" + "".join(f"#check @{n}\n" for n in names), encoding="utf-8")
    _, out = run(["lake", "env", "lean", str(probe)])
    absent = [n for n in names if f"Unknown identifier `{n}`" in out]
    if absent:
        report.update(stage="absent_name",
                      problems=[f"GapSolution.lean does not declare {n}" for n in absent])
        return finish(report, started, actor)

    cmd = ["lake", "comparator", "--config", "comparator_gap.json"]
    if "--paranoid" in args:
        cmd.append("--paranoid")
    sandbox = shutil.which("bwrap") is not None
    if not sandbox:
        cmd.append("--inadvisably-no-sandbox")
    code, out = run(cmd)
    report["sandbox"] = "bwrap" if sandbox else "off (no bwrap on this host)"
    if code != 0:
        report.update(stage="comparator", problems=[f"exit code {code}"], output=clean(out))
        return finish(report, started, actor)

    code, out = run(["lake", "env", "lean", "--run", "GapRunner.lean"])
    report.update(verdict="accept", stage="done",
                  question=[l for l in out.splitlines() if l.startswith(("who=", "event="))])
    return finish(report, started, actor)


if __name__ == "__main__":
    sys.exit(main())
