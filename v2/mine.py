#!/usr/bin/env python3
"""Hard Proof v2: find past logic bugs in small deterministic functions of our own repositories.

Each worker reads one slice of the history of one repository and writes `candidates.json`.

Usage:
    python3 mine.py plan
    python3 mine.py run [--only SLICE ...] [--concurrency 6]
    python3 mine.py merge
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from flowrun import run_agent

HERE = Path(__file__).resolve().parent
WORK = Path.home() / "Projects" / "hp-work"
OUT = WORK / "mine"

BRIEF = """You look for past bugs in the repository at `{repo}` (a local clone, read it with `git -C {repo} ...`, do not change it).

Your slice of the history: {slice_text}

Goal: a list of real bugs that were logic faults in a small function, where a precise statement of the intended behavior would have shown the fault. We want to study these bugs later, so each entry must be exact and checked.

Keep a bug only when all of these are true:
1. The fault was in one function, or in two functions that work as one unit, in Python code of the product (not a test, not a script, not UI code).
2. The result of the function depends only on its arguments, or on a small state that a test can simulate with a few values (a clock value, a process table, a small dict, a list of files). No network, no real subprocess, no thread timing.
3. The function at the fix has at most about 100 lines.
4. A concrete input exists for which the code before the fix gives a wrong result and the code after the fix gives the right result. You must give that input.
5. The fix commit exists in this clone and you read its diff.

How to work: read your slice, select entries that describe wrong behavior, find the fix commit with `git log --grep`, `git log -S` or the version tag, read the diff with `git show`, and read the function before the fix with `git show <parent>:<path>`. Reject an entry when you cannot confirm the fault in the code before the fix.

For each kept bug, also search for text that stated the intended behavior BEFORE the fix: a docstring, a comment, a help text, a README or docs sentence, or a changelog sentence of an earlier version. Quote it exactly with its file and the commit where you read it. If no such text existed, write null. Do not use text that the fix commit added.

Write one file, `candidates.json`, in the current folder (`{folder}`), and nothing else. It is a JSON list. Each entry:
{{
 "title": "short name of the bug",
 "repo": "{repo_name}",
 "fix_commit": "full sha",
 "parent_commit": "full sha of the commit before the fix",
 "file": "path of the file with the function",
 "function": "name (Class.method when it is a method)",
 "function_lines_at_parent": [first, last],
 "kind": "precedence | boundary | path or glob | parse | state | list or set logic | arithmetic | text | other",
 "what_was_wrong": "one or two sentences",
 "failing_input": "the concrete input, as a Python call or as values",
 "wrong_result": "result before the fix",
 "right_result": "result after the fix",
 "intended_behavior_text_before_fix": {{"text": "exact quote", "file": "path", "commit": "sha"}} or null,
 "state_needed": "none, or the small state that a test must simulate",
 "how_found": "user report | test | review | unknown (from the commit message or changelog)",
 "confidence": "high | medium"
}}

Quality is more important than count. Give the 3 to 8 best bugs of your slice. If the slice has none that pass, write an empty list. End with VERDICT: PASS when the file is written."""

CHECK = "python3 -c \"import json;d=json.load(open('candidates.json'));assert isinstance(d,list);[x['fix_commit'] and x['function'] for x in d];print(len(d))\""


def plan() -> list[dict]:
    slices = []
    pm = WORK / "Puppetmaster"
    n = len((pm / "docs" / "CHANGELOG.md").read_text(encoding="utf-8").splitlines())
    step = 480
    for i, start in enumerate(range(1, n + 1, step)):
        end = min(n, start + step - 1)
        slices.append({"id": f"pm-{i:02d}", "repo": str(pm), "repo_name": "Puppetmaster",
                       "slice_text": f"lines {start} to {end} of `docs/CHANGELOG.md` at HEAD (read them with `git -C {pm} show HEAD:docs/CHANGELOG.md | sed -n '{start},{end}p'`). The version headings give you the tags (`v1.2.3`)."})
    mn = WORK / "marionette"
    out = subprocess.run(["git", "-C", str(mn), "log", "--format=%H %s", "-i", "--grep=fix", "--", "harness", "pmharness"],
                         capture_output=True, text=True).stdout.splitlines()
    step = 70
    OUT.mkdir(parents=True, exist_ok=True)
    for i, start in enumerate(range(0, len(out), step)):
        part = out[start:start + step]
        listing = OUT / f"mn-{i:02d}.commits.txt"
        listing.write_text("\n".join(part) + "\n", encoding="utf-8")
        slices.append({"id": f"mn-{i:02d}", "repo": str(mn), "repo_name": "marionette",
                       "slice_text": f"the {len(part)} commits listed in `{listing}` (one line each: sha and subject; these commits touch `harness/` or `pmharness/` and have the word fix in the message). Read the file with `cat`."})
    (HERE / "mine_plan.json").write_text(json.dumps(slices, indent=1) + "\n", encoding="utf-8")
    return slices


def run_one(s: dict) -> dict:
    folder = OUT / s["id"]
    task = BRIEF.format(repo=s["repo"], repo_name=s["repo_name"], slice_text=s["slice_text"], folder=folder)
    r = run_agent(folder, f"hp2-mine-{s['id']}", task, ["candidates.json"], model="opus", shell=True, check=CHECK, timeout=3000)
    r["slice"] = s["id"]
    try:
        r["candidates"] = len(json.loads((folder / "candidates.json").read_text()))
    except Exception:
        r["candidates"] = None
    return r


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["plan", "run", "merge"])
    parser.add_argument("--only", nargs="*", default=[])
    parser.add_argument("--concurrency", type=int, default=6)
    args = parser.parse_args()
    if args.cmd == "plan":
        s = plan()
        print(json.dumps({"slices": len(s), "ids": [x["id"] for x in s]}))
        return 0
    slices = json.loads((HERE / "mine_plan.json").read_text())
    if args.cmd == "run":
        todo = [s for s in slices if not args.only or s["id"] in args.only]
        with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
            results = list(pool.map(run_one, todo))
        path = HERE / "mine_runs.json"
        old = json.loads(path.read_text()) if path.exists() else []
        done = {r["slice"] for r in results}
        path.write_text(json.dumps([r for r in old if r["slice"] not in done] + results, indent=1) + "\n", encoding="utf-8")
        print(json.dumps([{k: r.get(k) for k in ("slice", "flow_status", "candidates", "seconds", "cost_usd", "error")} for r in results], indent=1))
        return 0
    rows = []
    for s in slices:
        f = OUT / s["id"] / "candidates.json"
        if f.exists():
            for c in json.loads(f.read_text()):
                c["slice"] = s["id"]
                rows.append(c)
    (HERE / "bugs_raw.json").write_text(json.dumps(rows, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"bugs": len(rows), "by_repo": {r: sum(1 for x in rows if x.get("repo") == r) for r in {x.get("repo") for x in rows}}}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
