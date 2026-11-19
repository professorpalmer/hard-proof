"""Run the checks of the two swarm_policy domains again and store the results.

Run: python3 summarize.py --repo PATH_TO_MARIONETTE     writes summary.json
"""
from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
HP = HERE.parent / "tool" / "hp"


def hp(folder: str, *args: str) -> dict:
    done = subprocess.run([str(HP), *args], cwd=HERE / folder, capture_output=True, text=True, timeout=1800)
    return json.loads(done.stdout)


def kernels(result: dict) -> dict:
    stage = result["stages"][-1] if result.get("stages") else result
    report = stage.get("kernel_report") or result.get("kernel_report") or {}
    return {"verdict": result.get("verdict"), "accepted": report.get("accepted"), "rejected": report.get("rejected"),
            "crashed": report.get("crashed"), "seconds": result.get("seconds")}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True)
    args = parser.parse_args()
    repo = Path(args.repo).expanduser()
    commit = subprocess.run(["git", "-C", str(repo), "rev-parse", "--short=8", "HEAD"], capture_output=True, text=True).stdout.strip()
    ref = hp("swarm_policy", "check", "ref", "--paranoid")
    complete = hp("swarm_policy", "check", "complete", "--paranoid")
    link = hp("swarm_policy", "link", "--repo", str(repo), "--cases", "2000", "--mutants", "20")
    gap = hp("swarm_policy_docstring", "check", "gap", "--paranoid")
    question = hp("swarm_policy_docstring", "question")
    laws = [line.split()[1] for line in (HERE / "swarm_policy" / "Laws.lean").read_text().splitlines()
            if line.startswith("def ") and "Passes" not in line]
    out = {"function": "harness.pilot_guards.swarm_policy_table", "repository": "marionette", "commit": commit,
           "inputs": 4, "input_cases": 16, "laws": laws,
           "raw": {"ref": ref, "complete": complete, "link": link, "gap": gap, "question": question}}
    (HERE / "summary.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "raw"}, indent=1))
    for name in ("ref", "complete", "link", "gap", "question"):
        print("==", name, json.dumps(out["raw"][name])[:1400])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
