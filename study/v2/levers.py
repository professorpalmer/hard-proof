#!/usr/bin/env python3
"""Hard Proof v2: cost levers of a review worker, on a fixed sample of the known bugs.

Each arm reviews the same functions (the source before the fix). A finding detects the bug when its repro gives
a different result before and after the fix, so the score needs no judge. The arms differ in the Claude Code
arguments, the model, the effort or one line of the brief.

Usage:
    python3 levers.py run ARM [--n 24] [--concurrency 4]
    python3 levers.py score
"""
from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import random
import shutil
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import guard
import review
from bugs import PKG, SRC, WORK, run_snippet, same
from flowrun import run_agent

HERE = Path(__file__).resolve().parent
OUT = HERE / "levers"
RUNS = WORK / "lev"
APP = Path.home() / "Library" / "Application Support" / "puppetmaster" / "projects"
LEAN = ["--setting-sources", "", "--strict-mcp-config"]
TOOLS = ["--tools", "Bash,Read,Grep,Glob,Write,Edit", "--exclude-dynamic-system-prompt-sections"]
SHORT = ("You are a careful software engineer who works in a terminal. Use the tools to read files, run commands and "
         "write files. Do exactly what the task says. Keep your text short.")
NUDGE = ("The files of the project are large. Find the lines that you need with Grep, then read only those lines "
         "(Read with an offset and a limit). Do not read a whole file.\n\n")
ARMS = {
    "lean": {"model": "sonnet", "extra": LEAN},
    "tools": {"model": "sonnet", "extra": LEAN + TOOLS},
    "tools_short": {"model": "sonnet", "extra": LEAN + ["--tools", "Bash,Read,Grep,Glob,Write,Edit", "--system-prompt", SHORT]},
    "haiku": {"model": "claude-haiku-5-5", "extra": LEAN + TOOLS},
    "effort_low": {"model": "sonnet", "extra": LEAN + TOOLS, "effort": "low"},
    "nudge": {"model": "sonnet", "extra": LEAN + TOOLS, "brief": NUDGE},
    # hpflow 0.5: the direct runner with no Puppetmaster, and the default worker arguments of the tool.
    "direct": {"model": "sonnet", "extra": None, "direct": True},
    # The defaults of hpflow 0.5.0 as released: the tool list and no dynamic-section flag.
    "direct_final": {"model": "sonnet", "extra": None, "direct": True},
    # The review worker as hpflow 0.5 starts it: short system prompt and the read-less line.
    "direct_review": {"model": "sonnet", "extra": None, "direct": True, "reviewer": True},
    "short_nudge": {"model": "sonnet", "extra": LEAN + ["--tools", "Bash,Read,Grep,Glob,Write,Edit", "--system-prompt", SHORT], "brief": NUDGE},
}


def sample(n: int) -> list[dict]:
    bugs = sorted((b for b in json.loads((HERE / "bugs.json").read_text()) if b.get("verified")), key=lambda b: b["id"])
    return sorted(random.Random(1).sample(bugs, n), key=lambda b: b["id"])


def one(arm: str, b: dict) -> dict:
    spec = ARMS[arm]
    rid = hashlib.sha256(f"hp2lev|{arm}|{b['id']}".encode()).hexdigest()[:10]
    folder = RUNS / rid
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir(parents=True)
    shutil.copytree(SRC / b["id"] / "pre", folder / "project")
    task = review.BRIEF.format(function=b["function"], file=b["file"], top=PKG[b["repo"]][0],
                               arm_text=review.ARM_TEXT["shell"] + spec.get("brief", "") + (hint() if spec.get("reviewer") else ""))
    if spec.get("direct"):
        r = run_direct(folder, rid, task, bool(spec.get("reviewer")))
    else:
        r = run_agent(folder, f"hp2l-{rid}", task, ["findings.json", "finding_*.py"], model=spec["model"], shell=True,
                      check=review.CHECK, timeout=2400, effort=spec.get("effort"), extra_args=spec["extra"])
    r.update(run=rid, bug=b["id"], arm=arm)
    return r


def hint() -> str:
    sys.path.insert(0, str(HERE.parent / "tool"))
    from hpflow import adapters
    return adapters.review_hint("claude-code")


def run_direct(folder: Path, rid: str, task: str, reviewer: bool = False) -> dict:
    """One review worker through `hpflow.direct.DirectRunner`, as `hpf review` starts it."""
    import subprocess
    sys.path.insert(0, str(HERE.parent / "tool"))
    from hpflow import adapters
    from hpflow.direct import DirectRunner
    from hpflow.runner import agent_graph
    if not (folder / ".git").exists():
        for cmd in (["git", "init", "-q"], ["git", "add", "-A"],
                    ["git", "-c", "user.name=hp", "-c", "user.email=hp@localhost", "commit", "-q", "--allow-empty", "-m", "start"]):
            subprocess.run(cmd, cwd=folder, check=False, capture_output=True)
    payload = adapters.payload("claude-code", shell=True, lean=True, reviewer=reviewer)
    graph = agent_graph(f"hp2d-{rid}", task, ["findings.json", "finding_*.py"], "claude-code",
                        adapters.model_id("claude-code", "sonnet"), payload, check=review.CHECK, timeout=2400)
    with guard.slot():
        r = DirectRunner(RUNS / "_direct" / rid / "graphs").run(graph, folder)
    return {"flow_id": graph["id"], "folder": str(folder), "model": "sonnet", "flow_status": r.get("status"),
            "visits": sum(1 for s in r.get("steps", []) if s.get("node") == "work"), "seconds": r.get("seconds"),
            "cost_usd": r.get("cost_usd"), "logs": r.get("logs"), "error": r.get("error")}


def usage(rid: str) -> dict:
    tot = {"turns": 0, "in": 0, "cache_write": 0, "cache_read": 0, "out": 0}
    for f in glob.glob(str(RUNS / "_direct" / rid / "direct" / "*" / "*.stdout.txt")):
        for line in open(f, encoding="utf-8", errors="ignore"):
            if '"type":"result"' not in line.replace(" ", ""):
                continue
            try:
                e = json.loads(line)
            except Exception:
                continue
            tot["turns"] += e.get("num_turns") or 0
            for u in (e.get("modelUsage") or {}).values():
                tot["in"] += u.get("inputTokens", 0)
                tot["cache_write"] += u.get("cacheCreationInputTokens", 0)
                tot["cache_read"] += u.get("cacheReadInputTokens", 0)
                tot["out"] += u.get("outputTokens", 0)
    for f in glob.glob(str(APP / f"{rid}-*" / "jobs" / "*" / "tasks" / "*" / "invocations" / "*" / "claude_stdout.log")):
        for line in open(f, encoding="utf-8", errors="ignore"):
            if '"type":"result"' not in line.replace(" ", ""):
                continue
            try:
                e = json.loads(line)
            except Exception:
                continue
            tot["turns"] += e.get("num_turns") or 0
            for u in (e.get("modelUsage") or {}).values():
                tot["in"] += u.get("inputTokens", 0)
                tot["cache_write"] += u.get("cacheCreationInputTokens", 0)
                tot["cache_read"] += u.get("cacheReadInputTokens", 0)
                tot["out"] += u.get("outputTokens", 0)
    return tot


def run(arm: str, n: int, concurrency: int, rest: bool = False) -> int:
    bugs = sample(n)
    if rest:
        first = {b["id"] for b in bugs}
        bugs = [b for b in sample(sum(1 for x in json.loads((HERE / "bugs.json").read_text()) if x.get("verified"))) if b["id"] not in first]
    with ThreadPoolExecutor(max_workers=concurrency) as pool:
        results = list(pool.map(lambda b: one(arm, b), bugs))
    OUT.mkdir(exist_ok=True)
    (OUT / (f"{arm}.rest.json" if rest else f"{arm}.json")).write_text(json.dumps(results, indent=1) + "\n", encoding="utf-8")
    return score()


def score() -> int:
    bugs = {b["id"]: b for b in json.loads((HERE / "bugs.json").read_text())}
    table = {}
    arms: dict = {}
    for path in sorted(OUT.glob("*.json")):
        if path.name.startswith("score"):
            continue
        arms.setdefault(path.name.split(".")[0], []).extend(json.loads(path.read_text()))
    for name, rows in arms.items():
        s = {"runs": len(rows), "done": 0, "detected": 0, "findings": 0, "cost_usd": 0.0, "seconds": 0,
             "turns": 0, "in": 0, "cache_write": 0, "cache_read": 0, "out": 0, "detected_ids": []}
        for r in rows:
            b = bugs[r["bug"]]
            folder = RUNS / r["run"]
            s["done"] += 1 if r.get("flow_status") == "done" else 0
            s["cost_usd"] += r.get("cost_usd") or 0
            s["seconds"] += r.get("seconds") or 0
            for k, v in usage(r["run"]).items():
                s[k] += v
            try:
                findings = json.loads((folder / "findings.json").read_text())
            except Exception:
                findings = []
            s["findings"] += len(findings)
            hit = False
            for f in findings:
                snippet = folder / f"finding_{f.get('n')}.py"
                if snippet.exists() and not same(run_snippet(SRC / b["id"] / "pre", snippet), run_snippet(SRC / b["id"] / "post", snippet)):
                    hit = True
            if hit:
                s["detected"] += 1
                s["detected_ids"].append(r["bug"])
        s["cost_usd"] = round(s["cost_usd"], 2)
        s["usd_per_run"] = round(s["cost_usd"] / max(1, s["runs"]), 3)
        table[name] = s
    (OUT / "score.json").write_text(json.dumps(table, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({k: {x: v[x] for x in v if x != "detected_ids"} for k, v in table.items()}, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["run", "score"])
    parser.add_argument("arm", nargs="?", choices=sorted(ARMS))
    parser.add_argument("--n", type=int, default=24)
    parser.add_argument("--concurrency", type=int, default=4)
    parser.add_argument("--rest", action="store_true", help="the verified bugs that are not in the sample of --n")
    args = parser.parse_args()
    if args.cmd == "score":
        return score()
    if not args.arm:
        parser.error("run needs an arm")
    return run(args.arm, args.n, args.concurrency, args.rest)


if __name__ == "__main__":
    sys.exit(main())
