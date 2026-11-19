#!/usr/bin/env python3
"""Hard Proof gate, experiment 4.

The gate is deterministic. It makes no model call. It does four checks:

1. Law cone lock: the hash of each human-owned file must be the signed hash.
2. Structure: each law has a witness theorem, and each mutant has a kill theorem.
3. Build: `Solution.lean` must build, and it must declare each required name.
4. Proof: `lake comparator` must accept the solution against the challenge.

Usage:
    python3 gate.py sign --by NAME    write laws.lock.json (a human action)
    python3 gate.py check             run the gate, print a JSON report

Exit code: 0 for accept, 1 for reject, 2 when the gate cannot start.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path

LOCK_NAME = "laws.lock.json"
RUN_LOG = "runs.jsonl"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sign(root: Path, signer: str) -> int:
    laws = load_json(root / "laws.json")
    lock = {
        "signed_by": signer,
        "signed_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "files": {name: sha256(root / name) for name in laws["human_files"]},
    }
    (root / LOCK_NAME).write_text(json.dumps(lock, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(lock, indent=2))
    return 0


def check_cone(root: Path, laws: dict) -> list[str]:
    lock_path = root / LOCK_NAME
    if not lock_path.exists():
        return ["no signed lock file"]
    lock = load_json(lock_path)
    problems = []
    for name in laws["human_files"]:
        want = lock["files"].get(name)
        if want is None:
            problems.append(f"{name}: not in the signed lock")
        elif not (root / name).exists():
            problems.append(f"{name}: file is absent")
        elif sha256(root / name) != want:
            problems.append(f"{name}: hash is not the signed hash")
    return problems


def check_structure(root: Path, laws: dict) -> list[str]:
    names = set(load_json(root / "comparator.json")["theorem_names"])
    problems = []
    for law in laws["laws"]:
        for key in ("theorem", "witness"):
            if law.get(key) not in names:
                problems.append(f"law {law['id']}: {key} is not a comparator theorem")
    for mutant in laws["mutants"]:
        kills = [k for k in mutant.get("kills", []) if k in names]
        if not kills:
            problems.append(f"mutant {mutant['id']}: no kill theorem")
    return problems


def check_build(root: Path) -> str:
    """Build the solution. Return the compiler output when the build fails."""
    proc = subprocess.run(["lake", "build", "Solution"], cwd=root, capture_output=True, text=True)
    if proc.returncode == 0:
        return ""
    lines = (proc.stdout + proc.stderr).splitlines()
    return "\n".join(l for l in lines if not l.startswith("trace:"))


def absent_theorems(root: Path) -> list[str]:
    """Return each required name that the solution does not declare.

    `lake comparator` in Lean 4.36.0 stops with exit code 134 when a name is
    absent. This check gives the agent a clear message before that.
    """
    cfg = load_json(root / "comparator.json")
    names = cfg["theorem_names"] + cfg.get("definition_names", [])
    probe = root / ".lake" / "hp_names.lean"
    probe.parent.mkdir(exist_ok=True)
    probe.write_text("import Solution\n" + "".join(f"#check @{n}\n" for n in names),
                     encoding="utf-8")
    proc = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root,
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    return [n for n in names if f"Unknown identifier `{n}`" in out]


def run_comparator(root: Path, paranoid: bool) -> tuple[int, str, bool]:
    """Return (exit code, output, sandbox_on)."""
    sandbox_on = shutil.which("bwrap") is not None
    cmd = ["lake", "comparator"]
    if paranoid:
        cmd.append("--paranoid")
    if not sandbox_on:
        cmd.append("--inadvisably-no-sandbox")
    proc = subprocess.run(cmd, cwd=root, capture_output=True, text=True)
    return proc.returncode, (proc.stdout + proc.stderr).strip(), sandbox_on


def check(root: Path, paranoid: bool, actor: str) -> int:
    started = time.time()
    laws = load_json(root / "laws.json")
    report: dict = {
        "experiment": laws["experiment"],
        "verdict": "reject",
        "stage": "",
        "problems": [],
        "sandbox": None,
        "paranoid": paranoid,
    }

    problems = check_cone(root, laws)
    if problems:
        report.update(stage="law_cone_lock", problems=problems)
        return finish(root, report, started, actor)

    problems = check_structure(root, laws)
    if problems:
        report.update(stage="structure", problems=problems)
        return finish(root, report, started, actor)

    build_output = check_build(root)
    if build_output:
        report.update(stage="build", problems=["Solution.lean does not build"],
                      output=build_output[-6000:])
        return finish(root, report, started, actor)

    absent = absent_theorems(root)
    if absent:
        report.update(stage="absent_theorem",
                      problems=[f"Solution.lean does not declare {name}" for name in absent])
        return finish(root, report, started, actor)

    code, output, sandbox_on = run_comparator(root, paranoid)
    report["sandbox"] = "bwrap" if sandbox_on else "off (no bwrap on this host)"
    if code != 0:
        report.update(stage="comparator", problems=[f"exit code {code}"], output=output[-6000:])
        return finish(root, report, started, actor)

    lock = load_json(root / LOCK_NAME)
    report.update(
        verdict="accept",
        stage="done",
        signed_by=lock["signed_by"],
        laws=[
            {"id": law["id"], "grade": "P", "min_grade": law["min_grade"],
             "theorem": law["theorem"], "witness": law["witness"]}
            for law in laws["laws"]
        ],
        mutants=[{"id": m["id"], "killed_by": m["kills"]} for m in laws["mutants"]],
        recorded_facts=laws.get("recorded_facts", []),
        permitted_axioms=load_json(root / "comparator.json")["permitted_axioms"],
        assumptions=laws["assumptions"],
        link=laws["link"],
    )
    return finish(root, report, started, actor)


def finish(root: Path, report: dict, started: float, actor: str) -> int:
    report["seconds"] = round(time.time() - started, 2)
    print(json.dumps(report, indent=2))
    line = {
        "at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "actor": actor,
        "verdict": report["verdict"],
        "stage": report["stage"],
        "seconds": report["seconds"],
    }
    with (root / RUN_LOG).open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(line) + "\n")
    return 0 if report["verdict"] == "accept" else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Hard Proof gate, experiment 1")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    sub = parser.add_subparsers(dest="command", required=True)
    p_sign = sub.add_parser("sign")
    p_sign.add_argument("--by", required=True)
    p_check = sub.add_parser("check")
    p_check.add_argument("--paranoid", action="store_true")
    p_check.add_argument("--actor", default="agent")
    args = parser.parse_args()
    if not (args.root / "laws.json").exists():
        print("laws.json is absent", file=sys.stderr)
        return 2
    if args.command == "sign":
        return sign(args.root, args.by)
    return check(args.root, args.paranoid, args.actor)


if __name__ == "__main__":
    sys.exit(main())
