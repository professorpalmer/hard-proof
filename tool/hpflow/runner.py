"""Worker runs. A `Runner` takes a graph and a folder and returns a record. `hpflow.direct.DirectRunner` is the runner."""
from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, List, Optional


class Runner:
    """The one place where hpflow starts workers.

    `run` takes a flow graph and a folder. It returns a record with the keys `status`, `steps`
    (each with `node`, `ok`, `verdict`, `reason`, `jobs`, `seconds`, `cost_usd`), `jobs`,
    `cost_usd` and `seconds`. A record with the key `error` has no worker result. A `cost_usd` of None is unknown.
    """

    name = "custom"

    def run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        raise NotImplementedError


def agent_graph(flow_id: str, task: str, files: List[str], adapter: str, model: str, payload: Dict[str, Any],
                check: Optional[str] = None, repairs: int = 1, timeout: int = 3600, node: str = "work") -> Dict[str, Any]:
    """One agent node, an optional shell check with a repair edge, then end.

    `payload` comes from `adapters.payload`: the graph does not know the keys of an adapter."""
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
            "defaults": {"adapter": adapter, "model": model, "timeout_seconds": timeout, "finish": "criteria"},
            "nodes": nodes, "edges": edges}
