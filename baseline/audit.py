#!/usr/bin/env python3
"""Hard Proof: audit stored worker transcripts for an answer leak.

For each Claude Code transcript of a run folder, this script reports:
  outside   tool calls that name a path outside the run folder
  cue       sentences of the worker (text or thinking) that name the folder or its path

Usage:
    python3 audit.py <run folder> [<run folder> ...]
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

PROJECTS = Path.home() / ".claude" / "projects"


def transcript_dir(folder: Path) -> Path:
    return PROJECTS / re.sub(r"[^A-Za-z0-9]", "-", str(folder))


def audit(folder: Path) -> dict:
    out = {"folder": str(folder), "transcripts": 0, "tool_calls": 0, "outside": [], "cue": []}
    name = folder.parent.name if re.fullmatch(r"[a-z]+_\d+", folder.name) else folder.name
    cue = re.compile(r"(folder name|directory name|name of (the|this) (folder|directory)|path (says|suggests|contains|name)|"
                     + re.escape(name) + r")", re.I)
    for path in sorted(transcript_dir(folder).glob("*.jsonl")):
        out["transcripts"] += 1
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            try:
                msg = json.loads(line).get("message") or {}
            except Exception:
                continue
            if msg.get("role") != "assistant" or not isinstance(msg.get("content"), list):
                continue
            for part in msg["content"]:
                kind = part.get("type")
                if kind == "tool_use":
                    out["tool_calls"] += 1
                    text = json.dumps(part.get("input", {}))
                    paths = re.findall(r"(/Users/[^\s\"'\\;|&)]+|\.\./[^\s\"'\\;|&)]*)", text)
                    bad = [p for p in paths if p.startswith("..") or not p.startswith(str(folder))]
                    if bad:
                        out["outside"].append({"tool": part.get("name"), "paths": sorted(set(bad))[:5]})
                elif kind in ("text", "thinking"):
                    body = part.get("text") or part.get("thinking") or ""
                    for sentence in re.split(r"(?<=[.!?\n])\s+", body):
                        if cue.search(sentence):
                            out["cue"].append(sentence.strip()[:240])
    return out


def main() -> int:
    rows = [audit(Path(a).resolve()) for a in sys.argv[1:]]
    print(json.dumps({"folders": len(rows), "with_transcript": sum(1 for r in rows if r["transcripts"]),
                      "tool_calls": sum(r["tool_calls"] for r in rows),
                      "outside": [{"folder": r["folder"], "calls": r["outside"]} for r in rows if r["outside"]],
                      "cue": [{"folder": r["folder"], "sentences": r["cue"][:6]} for r in rows if r["cue"]]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
