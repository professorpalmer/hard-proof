#!/usr/bin/env python3
"""Hard Proof: say what kind of gap each accepted gap certificate shows.

For each run folder with an accepted gap certificate, this script runs the
question runner of that experiment and sorts the result into a kind.

Usage:
    python3 classify.py
"""
from __future__ import annotations

import json
import re
import subprocess
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def run_lines(folder: Path, runner: str) -> list[str]:
    proc = subprocess.run(["lake", "env", "lean", "--run", runner], cwd=folder, capture_output=True, text=True)
    return [l for l in proc.stdout.splitlines() if l.strip()]


def lock_kind(lines: list[str]) -> str:
    events = [l for l in lines if l.startswith("event=")]
    for l in events:
        a = re.search(r"A_inside=(\S+)", l).group(1)
        b = re.search(r"B_inside=(\S+)", l).group(1)
        if a != b:
            ev = re.search(r"event=(\w+)", l).group(1)
            return f"first difference after a {ev} event"
    return "no difference in the printed sets"


def sync_kind(lines: list[str]) -> str:
    def rows(prefix: str) -> list[str]:
        line = next(l for l in lines if l.startswith(prefix))
        body = line[len(prefix) + 1:-1]
        return [r.strip() for r in body.split(";") if r.strip()]
    a, b = rows("A_result="), rows("B_result=")
    if sorted(a) == sorted(b) and a != b:
        return "row order"
    if len(set(a)) < len(a) or len(set(b)) < len(b):
        return "a row two times"
    if len(a) != len(b):
        return "different number of rows"
    return "different row content"


def main() -> int:
    out: dict[str, dict] = {}
    jobs = [
        ("lock, 3 laws", [ROOT / "exp6" / m for m in ("haiku", "sonnet", "opus")]
         + sorted(HERE.glob("exp6_gap*/*/")), "GapSolution.lean", "GapRunner.lean", lock_kind),
        ("sync, 7 laws", [ROOT / "exp8" / f"c_{m}" for m in ("haiku", "sonnet", "opus")]
         + sorted(HERE.glob("exp8c_gap*/*/")), "SyncGapSolution.lean", "SyncGapRunner.lean", sync_kind),
    ]
    for name, folders, solution, runner, kind in jobs:
        counts: Counter = Counter()
        detail = []
        for folder in folders:
            if not (folder / solution).exists():
                continue
            k = kind(run_lines(folder, runner))
            counts[k] += 1
            detail.append({"run": str(folder.relative_to(ROOT)), "kind": k})
        out[name] = {"certificates": sum(counts.values()), "kinds": dict(counts), "detail": detail}
    (HERE / "gap_kinds.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    for name, v in out.items():
        print(name, v["certificates"], v["kinds"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
