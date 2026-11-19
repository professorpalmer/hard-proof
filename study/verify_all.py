#!/usr/bin/env python3
"""Hard Proof: run each gate again on each stored worker result.

The script reads the run records of the study, runs the gate of each run folder
again with the extra kernels, and compares the verdict with the recorded
verdict. It makes no model call.

Usage:
    python3 verify_all.py [--jobs 4] [--fast]

`--fast` runs the gates without `--paranoid` (one kernel).
Exit code: 0 when each verdict is the same as the record, else 1.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent

# Run-record stem prefix -> gate command of that task family.
GATES = {
    "exp6_gap": ["gap_gate.py", "check"],
    "x_exp6_gap": ["gap_gate.py", "check"],
    "exp7_complete": ["complete_gate.py", "check"],
    "x_exp7_complete": ["complete_gate.py", "check"],
    "exp8a_code": ["gate8.py", "check", "code"],
    "exp8c_gap": ["gate8.py", "check", "gap"],
    "exp8d_complete": ["gate8.py", "check", "gap", "complete"],
    "exp11": ["gate11.py", "check", "gap", "complete"],
}


def gate_for(stem: str) -> list[str] | None:
    for prefix in sorted(GATES, key=len, reverse=True):
        if stem.startswith(prefix):
            return GATES[prefix]
    return None


def jobs() -> list[dict]:
    out = []
    for path in sorted((ROOT / "reps").glob("*.json")):
        gate = gate_for(path.stem)
        if gate is None:
            continue
        for run in json.loads(path.read_text())["runs"]:
            folder = ROOT / "reps" / run["task"] / f"{run['model']}_{run['rep']}"
            out.append({"id": f"reps/{run['task']}/{run['model']}_{run['rep']}", "dir": folder, "gate": gate,
                        "recorded": run.get("pilot_gate"), "recorded_mode": run.get("pilot_gate_mode")})
    first = [("exp6", "", GATES["exp6_gap"]), ("exp7", "", GATES["exp7_complete"]), ("exp8", "a_", GATES["exp8a_code"]),
             ("exp8", "c_", GATES["exp8c_gap"]), ("exp8", "d_", GATES["exp8d_complete"])]
    for exp, prefix, gate in first:
        for model in ("haiku", "sonnet", "opus"):
            folder = ROOT / exp / f"{prefix}{model}"
            if folder.exists():
                out.append({"id": f"{exp}/{prefix}{model} (first run)", "dir": folder, "gate": gate,
                            "recorded": "accept", "recorded_mode": None})
    for exp, gate, pattern in (("exp10", "gate10.py", "a_*"), ("exp12", "gate12.py", "[ab]_*")):
        for folder in sorted((ROOT / exp).glob(pattern)):
            if folder.is_dir():
                out.append({"id": f"{exp}/{folder.name} (first laws)", "dir": folder, "gate": [gate, "check", "laws"],
                            "recorded": "accept", "recorded_mode": "laws"})
    for exp, gate, pattern in (("exp10", "gate10.py", "loop2_*"), ("exp12", "gate12.py", "loop_*"), ("exp12", "gate12.py", "loopb_*")):
        for result in sorted((ROOT / exp).glob(f"{pattern}/result.json")):
            for rnd in json.loads(result.read_text())["rounds"]:
                base = result.parent
                out.append({"id": f"{exp}/{base.name}/round{rnd['round']}_adversary",
                            "dir": base / f"round{rnd['round']}_adversary", "gate": [gate, "check", "gap", "complete"],
                            "recorded": rnd.get("pilot_gate"), "recorded_mode": rnd.get("mode")})
                if "law_gate" in rnd:
                    out.append({"id": f"{exp}/{base.name}/round{rnd['round']}_law",
                                "dir": base / f"round{rnd['round']}_law", "gate": [gate, "check", "laws"],
                                "recorded": rnd.get("law_gate"), "recorded_mode": "laws"})
    return out


def run_one(job: dict, paranoid: bool) -> dict:
    cmd = [sys.executable] + job["gate"] + (["--paranoid"] if paranoid and "laws" not in job["gate"] else []) + ["--actor", "verify-all"]
    started = time.time()
    proc = subprocess.run(cmd, cwd=job["dir"], capture_output=True, text=True)
    text = proc.stdout
    try:
        report = json.loads(text[text.find("{"): text.rfind("}") + 1])
        verdict, mode = report.get("verdict"), report.get("accepted_mode")
    except Exception:
        verdict, mode = "error", None
    same = verdict == job["recorded"] and (job["recorded_mode"] in (None, mode) or verdict != "accept")
    return {"id": job["id"], "recorded": job["recorded"], "now": verdict, "mode": mode, "same": same,
            "seconds": round(time.time() - started, 1)}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--fast", action="store_true")
    parser.add_argument("--only", default="", help="comma list of id prefixes; the results are merged into verify_all.json")
    args = parser.parse_args()
    todo = jobs()
    only = [x for x in args.only.split(",") if x]
    if only:
        todo = [j for j in todo if any(j["id"].startswith(x) for x in only)]
    started = time.time()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda j: run_one(j, not args.fast), todo))
    out_path = ROOT / "verify_all.json"
    if only and out_path.exists():
        done = {r["id"] for r in results}
        results = [r for r in json.loads(out_path.read_text())["results"] if r["id"] not in done] + results
    summary = {
        "gate_runs": len(results),
        "extra_kernels": not args.fast,
        "accept": sum(1 for r in results if r["now"] == "accept"),
        "reject": sum(1 for r in results if r["now"] == "reject"),
        "same_as_record": sum(1 for r in results if r["same"]),
        "different": [r for r in results if not r["same"]],
        "seconds": round(time.time() - started),
    }
    out_path.write_text(json.dumps({"summary": summary, "results": results}, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))
    return 0 if not summary["different"] else 1


if __name__ == "__main__":
    sys.exit(main())
