#!/usr/bin/env python3
"""Hard Proof, experiment 12: the link between the Lean model and the shipped code.

Each random case goes to two systems:

1. `Sync.ref`, the Lean model that the laws are proved for.
2. The real `puppetmaster.registry_sync.plan_starter_sync` from Puppetmaster.

The two results must be the same list of rows: id, adapter, model, enabled.

One part is replaced: `starter_registry()` returns the starter list of the case.
The real function reads the starter list from that call.

Usage:
    python3 sync_link.py [--cases N] [--seed N] [--pm PATH] [--mutant NAME]

Mutants (changed versions of the real code, to show that the test can fail):
    enable-ignores-lock   `--enable` also enables an entry on a locked adapter
    skip-identity-check   an entry with a known adapter and model is added again

Exit code: 0 when each case agrees, else 1.
"""
from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import time
from dataclasses import replace
from pathlib import Path

HERE = Path(__file__).resolve().parent
ADAPTERS = {1: "claude-code", 2: "cursor", 3: "codex"}


def rows_text(rows: list[tuple[int, int, int, int]]) -> str:
    return ";".join(",".join(str(x) for x in row) for row in rows)


def random_case(rng: random.Random, duplicates: bool = False):
    enable = rng.randint(0, 1)
    locked = sorted(a for a in ADAPTERS if rng.random() < 0.35)
    def row(i: int):
        return (i, rng.randint(1, 3), rng.randint(1, 4), rng.randint(0, 1))
    reg_ids = rng.sample(range(1, 13), rng.randint(0, 5))
    starter_ids = rng.sample(range(1, 13), rng.randint(0, 7))
    starter = [row(i) for i in starter_ids]
    if duplicates and starter:
        # A starter list with one entry two or more times (not a legal list in the corrected model).
        starter = starter + [rng.choice(starter) for _ in range(rng.randint(1, 2))]
        rng.shuffle(starter)
    return enable, locked, starter, [row(i) for i in reg_ids]


def run_model(cases) -> list[str]:
    text = "".join(f"{en}|{','.join(map(str, locked))}|{rows_text(st)}|{rows_text(reg)}\n"
                   for en, locked, st, reg in cases)
    proc = subprocess.run(["lake", "env", "lean", "--run", "SyncRunner.lean"], cwd=HERE,
                          input=text, capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit("model runner failed:\n" + proc.stderr[-2000:])
    return proc.stdout.split("\n")[: len(cases)]


def main() -> int:
    parser = argparse.ArgumentParser(description="Hard Proof link test, experiment 12")
    parser.add_argument("--cases", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--pm", type=Path, default=Path.home() / "Projects" / "Puppetmaster")
    parser.add_argument("--mutant", choices=["enable-ignores-lock", "skip-identity-check"], default=None)
    parser.add_argument("--duplicates", action="store_true", help="starter lists with one entry two or more times")
    args = parser.parse_args()
    started = time.time()

    sys.path.insert(0, str(args.pm))
    import puppetmaster
    from puppetmaster import registry_sync
    from puppetmaster.model_registry import ModelSpec

    if args.mutant == "enable-ignores-lock":
        real = registry_sync._synced_spec
        registry_sync._synced_spec = lambda spec, *, adapter_locked, enable: real(
            spec, adapter_locked=adapter_locked and not enable, enable=enable)
    if args.mutant == "skip-identity-check":
        registry_sync._execution_identity = lambda spec: ("unique", spec.id, "")

    def spec(row) -> ModelSpec:
        i, a, m, e = row
        return ModelSpec(id=f"id-{i}", adapter=ADAPTERS[a], adapter_model_name=f"model-{m}",
                         enabled=bool(e))

    back = {name: number for number, name in ADAPTERS.items()}

    def row_of(s: ModelSpec):
        return (int(s.id.split("-")[1]), back[s.adapter], int(s.adapter_model_name.split("-")[1]),
                1 if s.enabled else 0)

    rng = random.Random(args.seed)
    cases = [random_case(rng, args.duplicates) for _ in range(args.cases)]
    model = run_model(cases)

    differ = 0
    first = None
    added_total = 0
    covered_total = 0
    for case, model_line in zip(cases, model):
        enable, locked, st, reg = case
        starter_specs = [spec(r) for r in st]
        registry_sync.starter_registry = lambda specs=starter_specs: list(specs)
        allowed = [name for number, name in ADAPTERS.items() if number not in locked]
        additions, covered = registry_sync.plan_starter_sync(
            [spec(r) for r in reg], enabled_adapters=allowed, enable=bool(enable))
        code_rows = reg + [row_of(a.spec) for a in additions]
        added_total += len(additions)
        covered_total += len(covered)
        code_line = rows_text(code_rows)
        if code_line != model_line:
            differ += 1
            if first is None:
                first = {"enable": enable, "locked": locked, "starter": st, "registry": reg,
                         "model": model_line, "code": code_line}

    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=args.pm,
                            capture_output=True, text=True).stdout.strip()
    report = {
        "experiment": "exp8-link-registry-sync",
        "mutant": args.mutant,
        "verdict": "agree" if differ == 0 else "disagree",
        "link_grade": "T",
        "code": {"function": "puppetmaster.registry_sync.plan_starter_sync",
                 "version": getattr(puppetmaster, "__version__", "unknown"), "commit": commit},
        "cases": len(cases), "seed": args.seed, "cases_that_differ": differ, "first_difference": first,
        "coverage": {"rows_added": added_total, "starter_rows_covered_by_identity": covered_total},
        "simulated": ["registry_sync.starter_registry"],
        "seconds": round(time.time() - started, 2),
    }
    print(json.dumps(report, indent=2))
    return 0 if differ == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
