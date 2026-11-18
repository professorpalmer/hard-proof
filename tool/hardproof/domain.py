"""The domain folder: its paths, its configuration and its run log."""
from __future__ import annotations

import json
import re
import time
from pathlib import Path

AUTHOR_FILES = [
    "hardproof.json",
    "Types.lean",
    "Ref.lean",
    "Codec.lean",
    "link_adapter.py",
    "DESCRIPTION.md",
    "Laws.lean",
]

SOLUTION_FILES = {
    "ref": "RefPassesSolution",
    "conflict": "ConflictSolution",
    "gap": "GapSolution",
    "complete": "CompleteSolution",
}

RUN_LOG = "hardproof_runs.jsonl"
LOCK_FILE = "hardproof.lock.json"
GEN_DIR = "hp"
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class DomainError(Exception):
    """A problem with the domain folder that stops a command."""


class Domain:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.gen = self.root / GEN_DIR

    def path(self, name: str) -> Path:
        return self.root / name

    def config(self) -> dict:
        path = self.path("hardproof.json")
        if not path.exists():
            raise DomainError(f"{path} does not exist. This folder is not a domain.")
        try:
            cfg = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise DomainError(f"hardproof.json is not valid JSON: {exc}") from exc
        ns = cfg.get("namespace", "HP")
        if not isinstance(ns, str) or not IDENT.match(ns):
            raise DomainError("hardproof.json: `namespace` must be one Lean identifier.")
        py = cfg.get("python") or {}
        if not isinstance(py, dict) or not py.get("module") or not py.get("function"):
            raise DomainError("hardproof.json: `python` must have `module` and `function`.")
        banned = cfg.get("banned_in_laws", ["ref"])
        if not isinstance(banned, list) or not all(isinstance(b, str) for b in banned):
            raise DomainError("hardproof.json: `banned_in_laws` must be a list of words.")
        if "ref" not in banned:
            banned = ["ref"] + banned
        cfg["namespace"] = ns
        cfg["banned_in_laws"] = banned
        return cfg

    def log_run(self, actor: str, command: str, verdict: str, seconds: float, extra: dict) -> None:
        line = {"time": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "actor": actor, "command": command,
                "verdict": verdict, "seconds": seconds}
        line.update(extra)
        with self.path(RUN_LOG).open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(line, sort_keys=True) + "\n")

    def runs(self) -> list:
        path = self.path(RUN_LOG)
        if not path.exists():
            return []
        out = []
        for raw in path.read_text(encoding="utf-8").splitlines():
            raw = raw.strip()
            if not raw:
                continue
            try:
                out.append(json.loads(raw))
            except json.JSONDecodeError:
                continue
        return out
