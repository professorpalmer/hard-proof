"""Worker runs. A `Runner` takes a flow graph and a folder and returns a record."""
from __future__ import annotations

import json
import re
import threading
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from .common import ADAPTER, DEFAULT_CONCURRENCY, apply_cost_rule, model_id, sh

READ_TOOLS = ["Read", "Glob", "Grep", "Write", "Edit"]
SHELL_TOOLS = READ_TOOLS + [f"Bash({c}:*)" for c in (
    "cd", "ls", "pwd", "cat", "git", "grep", "rg", "wc", "head", "tail", "sed", "awk", "sort", "uniq", "find",
    "python3", "lake", "lean", "shasum", "mkdir", "cp", "mv", "diff", "echo", "test", "true")]
NO_NET = ["WebFetch", "WebSearch", "Task", "Agent", "NotebookEdit"]


class Runner:
    """The one place where hpflow starts workers.

    `run` takes a flow graph and a folder. It returns a record with the keys `status`, `steps`
    (each with `node`, `ok`, `verdict`, `reason`, `jobs`, `seconds`, `cost_usd`), `jobs`,
    `cost_usd` and `seconds`. A record with the key `error` has no worker result.
    """

    def run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        raise NotImplementedError


def agent_graph(flow_id: str, task: str, files: List[str], model: str, shell: bool = True, check: Optional[str] = None,
                repairs: int = 1, timeout: int = 3600, node: str = "work") -> Dict[str, Any]:
    """One agent node, an optional shell check with a repair edge, then end (as `flowrun.run_agent`)."""
    payload = {"allowed_tools": SHELL_TOOLS if shell else READ_TOOLS,
               "disallowed_tools": NO_NET + ([] if shell else ["Bash"])}
    nodes: List[Dict[str, Any]] = [
        {"id": node, "kind": "agent", "role": "code", "files": files, "task": task, "payload": payload},
        {"id": "done", "kind": "end", "status": "pass"}, {"id": "failed", "kind": "end", "status": "fail"}]
    if check:
        nodes.insert(1, {"id": "check", "kind": "shell", "command": check})
        edges = [{"from": node, "to": "check", "when": "ok"}, {"from": "check", "to": "done", "when": "ok"},
                 {"from": "check", "to": node, "when": "fail", "max": repairs},
                 {"from": "check", "to": "failed", "when": "fail"}, {"from": node, "to": "failed"}]
    else:
        edges = [{"from": node, "to": "done", "when": "ok"}, {"from": node, "to": "failed"}]
    return {"id": flow_id, "entry": node,
            "defaults": {"adapter": ADAPTER, "model": model_id(model), "timeout_seconds": timeout, "finish": "criteria"},
            "nodes": nodes, "edges": edges}


def parse_json(text: str) -> Dict[str, Any]:
    return json.loads(text[text.find("{"): text.rfind("}") + 1])


def graph_timeout(graph: Dict[str, Any]) -> int:
    return int((graph.get("defaults") or {}).get("timeout_seconds") or 3600)


class PuppetmasterRunner(Runner):
    """Runs a graph with `puppetmaster flow run` and `puppetmaster flow wait`, as `flowrun.py` does."""

    def __init__(self, graph_dir: Path, concurrency: int = DEFAULT_CONCURRENCY, wait_extra: int = 600):
        self.graph_dir = graph_dir
        self.wait_extra = wait_extra
        self.concurrency = max(1, concurrency)
        # At most this many flows run at one time, whatever the number of threads that call `run`.
        self.slots = threading.BoundedSemaphore(self.concurrency)

    def job_record(self, job: str, cwd: Path) -> Tuple[float, float]:
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

    def run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        with self.slots:
            return self._run(graph, folder)

    def _run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        folder.mkdir(parents=True, exist_ok=True)
        if not (folder / ".git").exists():
            sh(["git", "init", "-q"], folder)
            sh(["git", "add", "-A"], folder)
            sh(["git", "-c", "user.name=hp", "-c", "user.email=hp@localhost", "commit", "-q", "--allow-empty", "-m", "start"],
               folder)
        self.graph_dir.mkdir(parents=True, exist_ok=True)
        gpath = self.graph_dir / f"{graph['id']}.json"
        gpath.write_text(json.dumps(graph, indent=1), encoding="utf-8")
        timeout = graph_timeout(graph) * 3
        record: Dict[str, Any] = {"graph": str(gpath)}
        _, out = sh(["puppetmaster", "flow", "run", str(gpath)], folder)
        try:
            run_id = parse_json(out)["run_id"]
        except Exception:
            record.update(status="error", error="launch", detail=out[-600:])
            return record
        record["flow"] = run_id
        _, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", str(timeout + self.wait_extra)], folder,
                    timeout=timeout + self.wait_extra + 300)
        try:
            flow = parse_json(out)
        except Exception:
            record.update(status="error", error="wait", detail=out[-600:])
            return record
        steps, jobs = [], []
        for s in flow.get("steps", []):
            item: Dict[str, Any] = {"node": s.get("node"), "ok": s.get("ok"), "verdict": s.get("verdict"),
                                    "reason": str(s.get("reason"))[:400], "jobs": list(s.get("job_ids") or [])}
            if item["jobs"]:
                secs, cost = 0.0, 0.0
                for j in item["jobs"]:
                    a, b = self.job_record(j, folder)
                    secs += a
                    cost = max(cost, b)
                item.update(seconds=round(secs), reported_usd=cost)
                jobs.extend(item["jobs"])
            steps.append(item)
        nodes = apply_cost_rule(steps)
        record.update(status=flow.get("status"), steps=steps, jobs=jobs, node_cost_usd=nodes,
                      cost_usd=round(sum(nodes.values()), 4), seconds=sum(s.get("seconds") or 0 for s in steps))
        return record
