#!/usr/bin/env python3
"""Hard Proof, experiment 11: generate decision-table domains of growing size.

A domain has K boolean inputs and a rule that is a random decision tree with L
leaves. The law set has one law for each leaf. Two tasks come from one tree:

  gap       one leaf law is removed. An adversary must find the open case.
  complete  each leaf has its law. An adversary must prove that no gap is left.

This experiment has no real code and no link test. It measures how the
adversary step and the completeness proof scale with the size of the domain.

Usage:
    python3 gen11.py --k 6 --leaves 8 --seed 1 --out k06_l008
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXP10 = HERE.parent / "exp10" / "base"


def build_tree(rng: random.Random, bits: list[int], leaves: int):
    """Return a tree: ('leaf', bool) or ('node', bit, low, high) with `leaves` leaves."""
    if leaves == 1 or not bits:
        return ("leaf", rng.random() < 0.5)
    bit = rng.choice(bits)
    rest = [b for b in bits if b != bit]
    left = rng.randint(1, leaves - 1) if leaves > 2 else 1
    left = max(1, min(left, 2 ** len(rest), leaves - 1))
    right = leaves - left
    if right > 2 ** len(rest):
        right = 2 ** len(rest)
        left = leaves - right
    return ("node", bit, build_tree(rng, rest, left), build_tree(rng, rest, right))


def paths(tree, prefix=()):
    if tree[0] == "leaf":
        yield prefix, tree[1]
    else:
        _, bit, low, high = tree
        yield from paths(low, prefix + ((bit, False),))
        yield from paths(high, prefix + ((bit, True),))


def lean_expr(tree, indent="  ") -> str:
    if tree[0] == "leaf":
        return "true" if tree[1] else "false"
    _, bit, low, high = tree
    return f"(if c.b{bit} then {lean_expr(high)} else {lean_expr(low)})"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, required=True)
    parser.add_argument("--leaves", type=int, required=True)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--out", required=True)
    parser.add_argument("--blind", action="store_true",
                        help="no reference rule in the model, laws in random order with names Law0..LawN")
    args = parser.parse_args()
    rng = random.Random(args.seed)
    tree = build_tree(rng, list(range(args.k)), args.leaves)
    leaf_paths = list(paths(tree))
    removed = rng.randrange(len(leaf_paths))

    fields = "\n".join(f"  b{i} : Bool" for i in range(args.k))
    ref_block = "" if args.blind else f"/-- The reference rule. -/\ndef ref : Decide := fun c =>\n  {lean_expr(tree)}\n\n"
    model = f'''/-
Hard Proof, experiment 11. GENERATED FILE (human-owned).

A decision-table domain: {args.k} boolean inputs, a rule with {len(leaf_paths)} leaves. Seed {args.seed}.
-/

namespace Tbl

/-- The inputs of one decision. -/
structure Case where
{fields}
deriving DecidableEq, Repr

/-- A rule: one answer for each case. -/
abbrev Decide := Case → Bool

{ref_block}end Tbl
'''

    def laws(skip: int | None) -> str:
        defs, names = [], []
        kept = [(i, p, o) for i, (p, o) in enumerate(leaf_paths) if i != skip]
        if args.blind:
            order = random.Random(args.seed * 1000 + (0 if skip is None else 1))
            order.shuffle(kept)
        for j, (i, path, out) in enumerate(kept):
            if args.blind:
                path = list(path)
                order.shuffle(path)
            hyps = " → ".join(f"c.b{bit} = {'true' if val else 'false'}" for bit, val in path)
            body = f"∀ c : Case, {hyps + ' → ' if hyps else ''}f c = {'true' if out else 'false'}"
            name = f"Law{j}" if args.blind else f"Leaf{i}"
            defs.append(f"def {name} (f : Decide) : Prop := {body}")
            names.append(f"{name} f")
        groups = ""
        if len(names) > 200:
            # A flat conjunction of 500 laws is past Lean's recursion limit. Use groups of 16.
            chunks = [names[i:i + 16] for i in range(0, len(names), 16)]
            for j, chunk in enumerate(chunks):
                groups += f"def Group{j} (f : Decide) : Prop :=\n  " + " ∧\n  ".join(chunk) + "\n\n"
            names = [f"Group{j} f" for j in range(len(chunks))]
        conj = " ∧\n  ".join(names)
        defs.append("")
        defs.append(groups.rstrip())
        return ("/-\nHard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.\n-/\nimport Tbl\n\n"
                "namespace Tbl\n\n" + "\n".join(defs) + "\n\n/-- A rule passes when each law holds for it. -/\n"
                f"def Passes (f : Decide) : Prop :=\n  {conj}\n\nend Tbl\n")

    for task, skip in (("gap", removed), ("complete", None)):
        folder = HERE / f"{args.out}_{task}"
        if folder.exists():
            shutil.rmtree(folder)
        folder.mkdir(parents=True)
        (folder / "Tbl.lean").write_text(model, encoding="utf-8")
        (folder / "TblLaws.lean").write_text(laws(skip), encoding="utf-8")
        for name in ("RecoverGapChallenge.lean", "RecoverCompleteChallenge.lean", "comparator_gap.json",
                     "comparator_complete.json", "gate10.py"):
            text = (EXP10 / name).read_text(encoding="utf-8")
            text = text.replace("RecoverLaws", "TblLaws").replace("Recover", "Tbl").replace("experiment 10", "experiment 11")
            text = text.replace("gate10", "gate11").replace("exp10-agent-written-laws", "exp11-decision-tables")
            text = text.replace("an agent-written law set", "the generated law set")
            (folder / name.replace("Recover", "Tbl").replace("gate10", "gate11")).write_text(text, encoding="utf-8")
        show = " ".join(f"b{i}={{c.b{i}}}" for i in range(args.k))
        (folder / "TblGapRunner.lean").write_text(f'''/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). Prints the question for the human.
-/
import Tbl
import TblGapSolution

open Tbl

def main : IO Unit := do
  let c := TblGap.input
  IO.println s!"case: {show}"
  IO.println s!"rule A: {{TblGap.designA c}}"
  IO.println s!"rule B: {{TblGap.designB c}}"
  IO.println s!"reference rule: {{ref c}}"
'''.replace('  IO.println s!"reference rule: {ref c}"\n', '' if args.blind else '  IO.println s!"reference rule: {ref c}"\n'), encoding="utf-8")
        (folder / "lakefile.toml").write_text('''name = "exp11"
defaultTargets = ["Exp11"]

[[lean_lib]]
name = "Exp11"
roots = ["Tbl", "TblLaws", "TblGapChallenge", "TblCompleteChallenge"]

[[lean_lib]]
name = "GapWork"
roots = ["TblGapSolution"]

[[lean_lib]]
name = "CompleteWork"
roots = ["TblCompleteSolution"]
''', encoding="utf-8")
        (folder / "lean-toolchain").write_text("leanprover/lean4:v4.36.0\n", encoding="utf-8")
        (folder / ".gitignore").write_text(".lake/\n*_runs.jsonl\n", encoding="utf-8")
        (HERE / "meta").mkdir(exist_ok=True)
        (HERE / "meta" / f"{args.out}_{task}.json").write_text(json.dumps({
            "k": args.k, "leaves": len(leaf_paths), "seed": args.seed, "task": task, "blind": args.blind,
            "laws": len(leaf_paths) - (1 if skip is not None else 0),
            "removed_leaf": None if skip is None else {"index": skip, "path": [[b, v] for b, v in leaf_paths[skip][0]],
                                                       "cases_open": 2 ** (args.k - len(leaf_paths[skip][0]))},
        }, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"out": args.out, "k": args.k, "leaves": len(leaf_paths), "removed": removed,
                      "open_cases": 2 ** (args.k - len(leaf_paths[removed][0]))}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
