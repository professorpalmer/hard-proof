#!/usr/bin/env python3
"""Hard Proof, experiment 13: the blind table tasks of experiment 11 again, in neutral folders.

The run folders of experiment 11 had the word "gap" or "complete" in their path
and in the flow id. This script runs the same graphs (same brief, same tools,
same gate) in folders that have a hash for a name, outside this project.

Usage:
    python3 proof_neutral.py [--models haiku sonnet] [--concurrency 6]
"""
from __future__ import annotations

import argparse
import json
import shutil
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from baseline import HERE, ROOT, RUNS, parse_json, sh, one_run  # noqa: F401
import re
from datetime import datetime


def run_one(t: dict) -> dict:
    folder = RUNS / "proof" / t["id"]
    if folder.exists():
        shutil.rmtree(folder)
    shutil.copytree(ROOT / t["source"], folder, ignore=shutil.ignore_patterns("*_runs.jsonl", ".git", ".lake", "*Solution.lean"))
    graph = json.loads((ROOT / "exp11" / "graphs_b" / f"{Path(t['source']).name}_{t['model']}.json").read_text())
    graph["id"] = f"hp13-proof-{t['id']}"
    sh(["git", "init", "-q"], folder)
    sh(["git", "add", "-A"], folder)
    sh(["git", "commit", "-q", "-m", "start"], folder)
    gpath = folder / ".lake" / "graph.json"
    gpath.parent.mkdir(exist_ok=True)
    gpath.write_text(json.dumps(graph, indent=1), encoding="utf-8")
    result: dict = {"id": t["id"], "arm": "proof"}
    _, out = sh(["puppetmaster", "flow", "run", str(gpath)], folder)
    try:
        run_id = parse_json(out)["run_id"]
    except Exception:
        result.update(error="launch", detail=out[-400:])
        return result
    result["flow"] = run_id
    _, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", "3600"], folder, timeout=4000)
    try:
        flow = parse_json(out)
    except Exception:
        result.update(error="wait", detail=out[-400:])
        return result
    visits = [s for s in flow.get("steps", []) if s.get("node") == "prove"]
    seconds, cost = 0.0, 0.0
    for s in visits:
        for job in s.get("job_ids") or []:
            _, st = sh(["puppetmaster", "status", job], folder)
            try:
                j = json.loads(st)["job"]
                seconds += (datetime.fromisoformat(j["completed_at"]) - datetime.fromisoformat(j["created_at"])).total_seconds()
            except Exception:
                pass
            _, art = sh(["puppetmaster", "artifacts", job], folder)
            found = re.findall(r'total_cost_usd\\?":\s*([0-9.]+)', art)
            cost += float(found[-1]) if found else 0.0
    result.update(flow_status=flow.get("status"), visits=len(visits), verdicts=[s.get("verdict") for s in visits],
                  seconds=round(seconds), cost_usd=round(cost, 3))
    _, out = sh([sys.executable, "gate11.py", "check", "gap", "complete", "--paranoid", "--actor", "pilot-verify"], folder)
    try:
        report = parse_json(out)
        result["pilot_gate"], result["pilot_gate_mode"] = report.get("verdict"), report.get("accepted_mode")
    except Exception:
        result["pilot_gate"] = "error"
    result["correct"] = result.get("pilot_gate") == "accept" and result.get("pilot_gate_mode") == t["truth"]
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--models", nargs="+", default=["haiku", "sonnet"])
    parser.add_argument("--concurrency", type=int, default=6)
    args = parser.parse_args()
    todo = [t for t in json.loads((HERE / "tasks.json").read_text()) if t["family"] == "tbl" and t["model"] in args.models]
    started = time.time()
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(run_one, todo))
    path = HERE / "results_proof.json"
    old = json.loads(path.read_text())["runs"] if path.exists() else []
    done = {r["id"] for r in results}
    path.write_text(json.dumps({"arm": "proof", "runs": [r for r in old if r["id"] not in done] + results}, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"ran": len(results), "correct": sum(1 for r in results if r.get("correct")),
                      "cost_usd": round(sum(r.get("cost_usd") or 0 for r in results), 2), "seconds": round(time.time() - started),
                      "not_correct": [r["id"] for r in results if not r.get("correct")]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
