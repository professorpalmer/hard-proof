#!/usr/bin/env python3
"""Hard Proof v2: the review arms on the real bugs.

A reviewer agent gets the source before the fix and the name of one function.
It writes findings, each with a runnable repro. A script runs each repro
against the source before the fix and after the fix.

Arms: `plain` (read and write files only), `shell` (can run Python on the source).

Usage:
    python3 review.py run --arm plain|shell --model sonnet|opus [--side pre|post] [--only ID ...] [--concurrency N]
    python3 review.py score
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from bugs import PKG, SRC, WORK, run_snippet, same
from flowrun import run_agent

HERE = Path(__file__).resolve().parent
RUNS = WORK / "r"

BRIEF = """The folder `project/` has the Python source of a tool. Please review one function: `{function}` in `project/{file}`, with the helper functions that it calls.

Look for inputs for which this function gives a wrong result: a result that conflicts with its docstring, its comments, the documentation in `project/docs` or `project/README.md`, the name of the function, or what its callers in the project need. Only report a problem that you are sure about. If you find no problem, report none. Do not report style, speed, or missing features.

Write your report into the current folder:
- `findings.json`: a JSON list, the most certain finding first, at most 5 entries. Each entry: {{"n": 1, "claim": "what is wrong, in one or two sentences", "expected": "the result that a correct function gives for the input of the repro", "confidence": "high | medium"}}. An empty list when you find no problem.
- For each finding `n`, a file `finding_<n>.py` that defines `run()` with no arguments. `run()` imports the function from the project (the folder `project/` is the first entry of `sys.path`, so `import {top}` works), calls it on the input of your finding, and returns a short string that shows the result (use `repr`). If the function needs small state, build it inside `run()` with the standard library only. `run()` must be deterministic: no real time, no random values, no network, no paths outside a `tempfile.TemporaryDirectory()`. If the result is an exception, catch it and return its class name.

{arm_text}Do not change `project/`. End with VERDICT: PASS when the report is written."""

ARM_TEXT = {"plain": "You have no shell in this task. Read the code.\n\n",
            "shell": "You have a shell. You can run Python on the project to check a finding, for example `cd project && python3 -c \"...\"`.\n\n"}
CHECK = "python3 -c \"import json;d=json.load(open('findings.json'));assert isinstance(d,list) and len(d)<=5\""


def run_id(arm: str, model: str, side: str, bug: str) -> str:
    return hashlib.sha256(f"hp2r|{arm}|{model}|{side}|{bug}".encode()).hexdigest()[:10]


def one(arm: str, model: str, side: str, b: dict) -> dict:
    rid = run_id(arm, model, side, b["id"])
    folder = RUNS / rid
    if not (folder / "project").exists():
        folder.mkdir(parents=True, exist_ok=True)
        shutil.copytree(SRC / b["id"] / side, folder / "project")
    task = BRIEF.format(function=b["function"], file=b["file"], top=PKG[b["repo"]][0], arm_text=ARM_TEXT[arm])
    r = run_agent(folder, f"hp2-{rid}", task, ["findings.json", "finding_*.py"], model=model, shell=(arm == "shell"),
                  check=CHECK, timeout=2400)
    r.update(run=rid, bug=b["id"], arm=arm, side=side, model=model)
    return r


def head_tree(repo: str) -> Path:
    """The source of the newest commit of the clone, written one time."""
    dest = SRC / "_head" / repo
    if not dest.exists():
        dest.mkdir(parents=True)
        arch = subprocess.Popen(["git", "-C", str(WORK / repo), "archive", "HEAD", *PKG[repo]], stdout=subprocess.PIPE)
        subprocess.run(["tar", "-x", "-C", str(dest)], stdin=arch.stdout, check=False)
        arch.wait()
    return dest


def score() -> int:
    bugs = {b["id"]: b for b in json.loads((HERE / "bugs.json").read_text()) if b.get("verified")}
    runs = json.loads((HERE / "review_runs.json").read_text())
    rows = []
    for r in runs:
        b = bugs.get(r["bug"])
        if not b:
            continue
        folder = RUNS / r["run"]
        try:
            findings = json.loads((folder / "findings.json").read_text())
        except Exception:
            findings = None
        row = {k: r.get(k) for k in ("run", "bug", "arm", "side", "model", "seconds", "cost_usd", "flow_status")}
        row["findings"] = None if findings is None else len(findings)
        row["items"] = []
        for f in findings or []:
            snippet = folder / f"finding_{f.get('n')}.py"
            if not snippet.exists():
                row["items"].append({"n": f.get("n"), "state": "no repro file"})
                continue
            pre = run_snippet(SRC / b["id"] / "pre", snippet)
            post = run_snippet(SRC / b["id"] / "post", snippet)
            head = run_snippet(head_tree(b["repo"]), snippet)
            # A finding is "changed later" when the newest release gives a different result than the code under review,
            # and both runs returned a value (a moved or renamed function gives an error, which says nothing).
            later = bool(pre.get("ok") and head.get("ok") and pre["result"] != head["result"])
            row["items"].append({"n": f.get("n"), "claim": str(f.get("claim"))[:300], "expected": str(f.get("expected"))[:200],
                                 "pre": pre, "post": post, "head": head, "hits_the_fix": not same(pre, post),
                                 "changed_later": later})
        row["detected"] = any(i.get("hits_the_fix") for i in row["items"])
        row["first_hit"] = next((i["n"] for i in row["items"] if i.get("hits_the_fix")), None)
        row["other_findings"] = sum(1 for i in row["items"] if not i.get("hits_the_fix"))
        row["other_changed_later"] = sum(1 for i in row["items"] if not i.get("hits_the_fix") and i.get("changed_later"))
        rows.append(row)
    summary = {}
    for r in rows:
        key = f"{r['arm']}/{r['model']}/{r['side']}"
        s = summary.setdefault(key, {"runs": 0, "detected": 0, "findings": 0, "other_findings": 0, "cost_usd": 0.0, "seconds": 0})
        s["runs"] += 1
        s["detected"] += 1 if r["detected"] else 0
        s["findings"] += r["findings"] or 0
        s["other_findings"] += r["other_findings"]
        s["other_changed_later"] = s.get("other_changed_later", 0) + r["other_changed_later"]
        s["cost_usd"] = round(s["cost_usd"] + (r["cost_usd"] or 0), 2)
        s["seconds"] += r["seconds"] or 0
    (HERE / "review_score.json").write_text(json.dumps({"summary": summary, "rows": rows}, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["run", "score"])
    parser.add_argument("--arm", choices=["plain", "shell"], default="shell")
    parser.add_argument("--model", default="sonnet")
    parser.add_argument("--side", choices=["pre", "post"], default="pre")
    parser.add_argument("--only", nargs="*", default=[])
    parser.add_argument("--concurrency", type=int, default=8)
    args = parser.parse_args()
    if args.cmd == "score":
        return score()
    bugs = [b for b in json.loads((HERE / "bugs.json").read_text()) if b.get("verified") and (not args.only or b["id"] in args.only)]
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(lambda b: one(args.arm, args.model, args.side, b), bugs))
    path = HERE / "review_runs.json"
    old = json.loads(path.read_text()) if path.exists() else []
    done = {r["run"] for r in results}
    path.write_text(json.dumps([r for r in old if r["run"] not in done] + results, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"ran": len(results), "errors": [r for r in results if r.get("error")],
                      "cost_usd": round(sum(r.get("cost_usd") or 0 for r in results), 2)}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
