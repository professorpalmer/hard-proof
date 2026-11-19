#!/usr/bin/env python3
"""Hard Proof v2: start one Puppetmaster flow with one Claude Code worker and collect its record.

The worker runs in `folder` (a git repository is made there if absent). The
record has the flow id, the job ids, the worker time and the reported cost.
"""
from __future__ import annotations

import json
import re
import subprocess
from datetime import datetime
from pathlib import Path

import guard

MODELS = {"haiku": "claude-haiku-5-5", "sonnet": "claude-sonnet-5-5", "opus": "claude-opus-5-5"}
READ_TOOLS = ["Read", "Glob", "Grep", "Write", "Edit"]
SHELL_TOOLS = READ_TOOLS + [f"Bash({c}:*)" for c in (
    "cd", "ls", "pwd", "cat", "git", "grep", "rg", "wc", "head", "tail", "sed", "awk", "sort", "uniq", "find",
    "python3", "lake", "lean", "shasum", "mkdir", "cp", "mv", "diff", "echo", "test", "true")]
NO_NET = ["WebFetch", "WebSearch", "Task", "Agent", "NotebookEdit"]


def sh(cmd: list[str], cwd: Path, timeout: int = 600) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return 124, "timeout"


def parse_json(text: str) -> dict:
    return json.loads(text[text.find("{"): text.rfind("}") + 1])


def job_record(job: str, cwd: Path) -> tuple[float, float]:
    seconds, cost = 0.0, 0.0
    _, st = sh(["puppetmaster", "status", job], cwd)
    try:
        j = json.loads(st)["job"]
        seconds = (datetime.fromisoformat(j["completed_at"]) - datetime.fromisoformat(j["created_at"])).total_seconds()
    except Exception:
        pass
    _, art = sh(["puppetmaster", "artifacts", job], cwd)
    found = re.findall(r'total_cost_usd\\?":\s*([0-9.]+)', art)
    cost = float(found[-1]) if found else 0.0
    return seconds, cost


def run_agent(folder: Path, flow_id: str, task: str, files: list[str], model: str = "opus", shell: bool = True,
              check: str | None = None, repairs: int = 1, timeout: int = 3600, node: str = "work",
              extra_allowed: list[str] | None = None, effort: str | None = None) -> dict:
    """One agent node, an optional shell check with a repair edge, then end."""
    folder.mkdir(parents=True, exist_ok=True)
    if not (folder / ".git").exists():
        sh(["git", "init", "-q"], folder)
        sh(["git", "add", "-A"], folder)
        sh(["git", "-c", "user.name=hp", "-c", "user.email=hp@localhost", "commit", "-q", "--allow-empty", "-m", "start"], folder)
    allowed = (SHELL_TOOLS if shell else READ_TOOLS) + (extra_allowed or [])
    payload = {"allowed_tools": allowed, "disallowed_tools": NO_NET + ([] if shell else ["Bash"])}
    agent = {"id": node, "kind": "agent", "role": "code", "files": files, "task": task, "payload": payload}
    if effort:
        agent["effort"] = effort
    nodes = [agent,
             {"id": "done", "kind": "end", "status": "pass"}, {"id": "failed", "kind": "end", "status": "fail"}]
    if check:
        nodes.insert(1, {"id": "check", "kind": "shell", "command": check})
        edges = [{"from": node, "to": "check", "when": "ok"}, {"from": "check", "to": "done", "when": "ok"},
                 {"from": "check", "to": node, "when": "fail", "max": repairs}, {"from": "check", "to": "failed", "when": "fail"},
                 {"from": node, "to": "failed"}]
    else:
        edges = [{"from": node, "to": "done", "when": "ok"}, {"from": node, "to": "failed"}]
    graph = {"id": flow_id, "entry": node,
             "defaults": {"adapter": "claude-code", "model": MODELS.get(model, model), "timeout_seconds": timeout, "finish": "criteria"},
             "nodes": nodes, "edges": edges}
    gdir = Path.home() / "Projects" / "hp-work" / "graphs"
    gdir.mkdir(parents=True, exist_ok=True)
    gpath = gdir / f"{flow_id}.json"
    gpath.write_text(json.dumps(graph, indent=1), encoding="utf-8")
    result: dict = {"flow_id": flow_id, "folder": str(folder), "model": model}
    with guard.slot():
        _, out = sh(["puppetmaster", "flow", "run", str(gpath)], folder)
        try:
            run_id = parse_json(out)["run_id"]
        except Exception:
            result.update(error="launch", detail=out[-600:])
            return result
        result["flow"] = run_id
        _, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", str(timeout + 600)], folder, timeout=timeout + 900)
    try:
        flow = parse_json(out)
    except Exception:
        result.update(error="wait", detail=out[-600:])
        return result
    visits = [s for s in flow.get("steps", []) if s.get("node") == node]
    # A repair visit resumes the session of the worker, and Claude Code then reports the cost of the
    # session so far. So the cost of the node is the largest value, not the sum.
    seconds, cost, jobs = 0.0, 0.0, []
    for s in visits:
        for job in s.get("job_ids") or []:
            jobs.append(job)
            a, b = job_record(job, folder)
            seconds += a
            cost = max(cost, b)
    result.update(flow_status=flow.get("status"), visits=len(visits), verdicts=[s.get("verdict") for s in visits],
                  jobs=jobs, seconds=round(seconds), cost_usd=round(cost, 3))
    return result
