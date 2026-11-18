#!/usr/bin/env python3
"""Hard Proof, experiment 8: the gate for the registry sync domain.

Modes (each one is a `lake comparator` check of one solution file):

  code      `SyncSolution.lean`: the model of the shipped code obeys each law.
  gap       `SyncGapSolution.lean`: two designs pass each law and differ on one input.
  complete  `SyncCompleteSolution.lean`: two designs that pass each law give the
            same result on each input.

The gate accepts when one of the named modes is accepted. It makes no model call.

Usage:
    python3 gate8.py check MODE [MODE...] [--paranoid]

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
RUN_LOG = "gate8_runs.jsonl"
MODES = {
    "code": ("SyncSolution", "comparator_sync.json"),
    "gap": ("SyncGapSolution", "comparator_syncgap.json"),
    "complete": ("SyncCompleteSolution", "comparator_synccomplete.json"),
}


def run(cmd: list[str], stdin: str | None = None) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, input=stdin)
    return proc.returncode, (proc.stdout + proc.stderr)


def clean(text: str) -> str:
    keep = [l for l in text.splitlines() if not l.startswith(("trace:", "Exporting"))]
    return "\n".join(keep)[-5000:]


def check_mode(mode: str, paranoid: bool) -> dict:
    module, config = MODES[mode]
    result: dict = {"mode": mode, "verdict": "reject", "stage": "", "problems": []}
    if not (ROOT / f"{module}.lean").exists():
        result.update(stage="absent_file", problems=[f"{module}.lean does not exist"])
        return result
    code, out = run(["lake", "build", module])
    if code != 0:
        result.update(stage="build", problems=[f"{module}.lean does not build"], output=clean(out))
        return result
    cfg = json.loads((ROOT / config).read_text(encoding="utf-8"))
    names = cfg["theorem_names"] + cfg["definition_names"]
    probe = ROOT / ".lake" / f"{mode}_names.lean"
    probe.write_text(f"import {module}\n" + "".join(f"#check @{n}\n" for n in names), encoding="utf-8")
    _, out = run(["lake", "env", "lean", str(probe)])
    absent = [n for n in names if f"Unknown identifier `{n}`" in out]
    if absent:
        result.update(stage="absent_name", problems=[f"{module}.lean does not declare {n}" for n in absent])
        return result
    cmd = ["lake", "comparator", "--config", config]
    if paranoid:
        cmd.append("--paranoid")
    if shutil.which("bwrap") is None:
        cmd.append("--inadvisably-no-sandbox")
    code, out = run(cmd)
    if code != 0:
        result.update(stage="comparator", problems=[f"exit code {code}"], output=clean(out))
        return result
    result.update(verdict="accept", stage="done")
    if mode == "gap" and (ROOT / "SyncGapRunner.lean").exists():
        _, out = run(["lake", "env", "lean", "--run", "SyncGapRunner.lean"])
        result["question"] = [l for l in out.splitlines() if l.strip()]
    return result


def main() -> int:
    args = sys.argv[1:]
    modes = [a for a in args[1:] if a in MODES]
    if not args or args[0] != "check" or not modes:
        print(__doc__)
        return 2
    actor = args[args.index("--actor") + 1] if "--actor" in args else "agent"
    started = time.time()
    results = [check_mode(mode, "--paranoid" in args) for mode in modes]
    accepted = [r for r in results if r["verdict"] == "accept"]
    present = [r for r in results if r["stage"] != "absent_file"]
    report = {
        "experiment": "exp8-registry-sync",
        "verdict": "accept" if accepted else "reject",
        "accepted_mode": accepted[0]["mode"] if accepted else None,
        "results": present if present else results,
        "sandbox": "bwrap" if shutil.which("bwrap") else "off (no bwrap on this host)",
        "seconds": round(time.time() - started, 2),
    }
    print(json.dumps(report, indent=2))
    with (ROOT / RUN_LOG).open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "actor": actor, "modes": modes,
                             "verdict": report["verdict"], "mode": report["accepted_mode"],
                             "seconds": report["seconds"]}) + "\n")
    return 0 if accepted else 1


if __name__ == "__main__":
    sys.exit(main())
