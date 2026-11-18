#!/usr/bin/env python3
"""Hard Proof: repeat one worker task N times for each model, then verify each run.

Each run gets its own folder (a copy of the base, with a local git commit), one
Puppetmaster flow, and one worker. After the flow ends, this script runs the
gate again with the extra kernels and records the outcome, the time, and the
cost that the provider reported.

Usage:
    python3 run_reps.py --name NAME --base DIR --graph-template PATH_WITH_{model}
        --models haiku sonnet --n 5 --gate "python3 gate.py check ..." [--expect accept|objection]

Outcome of one run:
    accept      the pilot gate accepts the worker result
    objection   the worker ended with VERDICT: FAIL and changed no tracked file
    reject      the flow ended and the pilot gate does not accept
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sh(cmd: list[str], cwd: Path, timeout: int | None = None) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return proc.returncode, proc.stdout + proc.stderr


def parse_json(text: str) -> dict:
    return json.loads(text[text.find("{"): text.rfind("}") + 1])


def one_run(name: str, base: Path, graph: Path, model: str, index: int, gate: list[str]) -> dict:
    run_dir = HERE / name / f"{model}_{index}"
    if run_dir.exists():
        shutil.rmtree(run_dir)
    shutil.copytree(base, run_dir, ignore=shutil.ignore_patterns("*_runs.jsonl", ".git"))
    sh(["git", "init", "-q"], run_dir)
    sh(["git", "add", "-A"], run_dir)
    sh(["git", "commit", "-q", "-m", f"baseline {name} {model} {index}"], run_dir)
    result: dict = {"task": name, "model": model, "rep": index, "dir": str(run_dir)}
    code, out = sh(["puppetmaster", "flow", "run", str(graph)], run_dir)
    try:
        run_id = parse_json(out)["run_id"]
    except Exception:
        result.update(outcome="launch_error", detail=out[-400:])
        return result
    result["flow"] = run_id
    code, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", "3600"], run_dir, timeout=4000)
    try:
        flow = parse_json(out)
    except Exception:
        result.update(outcome="wait_error", detail=out[-400:])
        return result
    steps = flow.get("steps", [])
    visits = [s for s in steps if s.get("node") == "prove"]
    result["flow_status"] = flow.get("status")
    result["worker_visits"] = len(visits)
    result["worker_verdicts"] = [s.get("verdict") for s in visits]
    errors = [s.get("error") for s in visits if s.get("error")]
    if errors:
        result["error"] = errors[0][:300]
    seconds = 0.0
    cost = 0.0
    cost_known = True
    for s in visits:
        for job in s.get("job_ids") or []:
            _, st = sh(["puppetmaster", "status", job], run_dir)
            try:
                j = json.loads(st)["job"]
                seconds += (datetime.fromisoformat(j["completed_at"]) - datetime.fromisoformat(j["created_at"])).total_seconds()
            except Exception:
                pass
            _, art = sh(["puppetmaster", "artifacts", job], run_dir)
            found = re.findall(r'total_cost_usd\\?":\s*([0-9.]+)', art)
            if found:
                cost += float(found[-1])
            else:
                cost_known = False
    result["worker_seconds"] = round(seconds)
    result["cost_usd"] = round(cost, 2) if cost_known else None
    _, status = sh(["git", "status", "--short", "--untracked-files=all"], run_dir)
    changed = [l[3:] for l in status.splitlines() if l.strip()]
    result["changed_files"] = changed
    code, out = sh(gate, run_dir)
    try:
        report = parse_json(out)
        result["pilot_gate"] = report.get("verdict")
        result["pilot_gate_mode"] = report.get("accepted_mode")
    except Exception:
        result["pilot_gate"] = "error"
    last_verdict = result["worker_verdicts"][-1] if result["worker_verdicts"] else None
    if result["pilot_gate"] == "accept":
        result["outcome"] = "accept"
    elif last_verdict == "FAIL" and not changed:
        result["outcome"] = "objection"
    else:
        result["outcome"] = "reject"
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--name", required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--graph-template", required=True)
    parser.add_argument("--models", nargs="+", required=True)
    parser.add_argument("--n", type=int, default=5)
    parser.add_argument("--gate", required=True)
    parser.add_argument("--concurrency", type=int, default=6)
    args = parser.parse_args()
    base = args.base.resolve()
    gate = args.gate.split()
    jobs = []
    for model in args.models:
        graph = Path(args.graph_template.format(model=model)).resolve()
        for i in range(1, args.n + 1):
            jobs.append((args.name, base, graph, model, i, gate))
    started = time.time()
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(lambda j: one_run(*j), jobs))
    out = HERE / f"{args.name}.json"
    out.write_text(json.dumps({"task": args.name, "seconds": round(time.time() - started),
                               "runs": results}, indent=1) + "\n", encoding="utf-8")
    for model in args.models:
        rows = [r for r in results if r["model"] == model]
        counts: dict[str, int] = {}
        for r in rows:
            counts[r["outcome"]] = counts.get(r["outcome"], 0) + 1
        print(args.name, model, counts)
    return 0


if __name__ == "__main__":
    sys.exit(main())
