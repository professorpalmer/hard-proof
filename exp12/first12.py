#!/usr/bin/env python3
"""Hard Proof, experiment 12: one agent writes the first law set from DESCRIPTION.md.

Usage: python3 first12.py --model claude-sonnet-5-5 --name a_sonnet
"""
from __future__ import annotations

import argparse
import json
import shutil
import sys

from loop12 import BASE, FIRST_TASK, HERE, LAW_HUMAN, graph, law_names, parse_json, pins, run_flow, sh


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--name", required=True)
    args = parser.parse_args()
    folder = HERE / args.name
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir()
    for f in LAW_HUMAN + [".gitignore", "lake-manifest.json"]:
        shutil.copy(BASE / f, folder / f)
    check = f"printf '%s  %s\\n' {pins(folder, LAW_HUMAN)} | shasum -a 256 -c - && python3 gate12.py check laws --actor flow"
    flow = run_flow(folder, graph(f"hardproof-exp12-{args.name.replace('_', '-')}", args.model, ["SyncLaws.lean"], FIRST_TASK, check))
    _, out = sh([sys.executable, "gate12.py", "check", "laws", "--actor", "pilot-verify"], folder)
    report = parse_json(out)
    text = (folder / "SyncLaws.lean").read_text(encoding="utf-8") if (folder / "SyncLaws.lean").exists() else ""
    result = {"name": args.name, "model": args.model, "flow": flow, "pilot_gate": report.get("verdict"), "laws": law_names(text)}
    (folder / "first_result.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
