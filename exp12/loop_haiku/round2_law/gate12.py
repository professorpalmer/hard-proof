#!/usr/bin/env python3
"""Hard Proof, experiment 12: the gate for agent-written laws.

Modes:

  laws      `SyncLaws.lean`: an agent wrote the laws. The file must build,
            must declare `Sync.Passes`, a proof `Sync.ref_passes` that the
            mirror of the shipped code passes each law, and a proof
            `Sync.some_design_fails` that the laws reject some rule. The text
            before `theorem ref_passes` must not mention `ref` or `adjust`.
  gap       `SyncGapSolution.lean`: two designs pass each law and differ on one input.
  complete  `SyncCompleteSolution.lean`: two designs that pass each law agree on each legal input.

`gap` and `complete` are `lake comparator` checks. The gate accepts when one of
the named modes is accepted. It makes no model call.

Usage:
    python3 gate12.py check MODE [MODE...] [--paranoid]
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RUN_LOG = "gate12_runs.jsonl"
PERMITTED = {"propext", "Quot.sound", "Classical.choice"}
MODES = {
    "gap": ("SyncGapSolution", "comparator_gap.json"),
    "complete": ("SyncCompleteSolution", "comparator_complete.json"),
}


def run(cmd: list[str]) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return proc.returncode, (proc.stdout + proc.stderr)


def clean(text: str) -> str:
    keep = [l for l in text.splitlines() if not l.startswith(("trace:", "Exporting"))]
    return "\n".join(keep)[-5000:]


def check_laws() -> dict:
    result: dict = {"mode": "laws", "verdict": "reject", "stage": "", "problems": []}
    path = ROOT / "SyncLaws.lean"
    if not path.exists():
        result.update(stage="absent_file", problems=["SyncLaws.lean does not exist"])
        return result
    text = path.read_text(encoding="utf-8")
    code = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    code = re.sub(r"--[^\n]*", " ", code)
    if "theorem ref_passes" not in code:
        result.update(stage="text", problems=["SyncLaws.lean does not declare `theorem ref_passes`"])
        return result
    before = code.split("theorem ref_passes")[0]
    problems = []
    for banned in ("ref", "adjust"):
        if re.search(rf"(?<![A-Za-z0-9_]){banned}(?![A-Za-z0-9_])", before):
            problems.append(f"a law mentions `{banned}` (the text before `theorem ref_passes` must not name it)")
    for word in ("sorry", "native_decide"):
        if re.search(rf"\b{word}\b", code):
            problems.append(f"the file uses `{word}`")
    if re.search(r"^\s*axiom\b", code, flags=re.M):
        problems.append("the file declares an axiom")
    if problems:
        result.update(stage="text", problems=problems)
        return result
    code_rc, out = run(["lake", "build", "SyncLaws"])
    if code_rc != 0:
        result.update(stage="build", problems=["SyncLaws.lean does not build"], output=clean(out))
        return result
    probe = ROOT / ".lake" / "laws_check.lean"
    probe.write_text(
        "import SyncLaws\n"
        "example : Sync.SyncImpl → Prop := Sync.Passes\n"
        "theorem HardProofGate.ref_passes : Sync.Passes Sync.ref := Sync.ref_passes\n"
        "theorem HardProofGate.some_design_fails : ∃ f : Sync.SyncImpl, ¬ Sync.Passes f := Sync.some_design_fails\n"
        "#print axioms HardProofGate.ref_passes\n"
        "#print axioms HardProofGate.some_design_fails\n", encoding="utf-8")
    code_rc, out = run(["lake", "env", "lean", str(probe)])
    if code_rc != 0 or "error" in out:
        result.update(stage="statement", problems=["the required declarations are absent or have a different statement"],
                      output=clean(out))
        return result
    used = set()
    for line in out.splitlines():
        m = re.search(r"depends on axioms: \[(.*)\]", line)
        if m:
            used |= {a.strip() for a in m.group(1).split(",") if a.strip()}
    bad = sorted(used - PERMITTED)
    if bad:
        result.update(stage="axioms", problems=[f"axiom not permitted: {a}" for a in bad])
        return result
    laws = re.findall(r"^\s*def\s+([A-Za-z0-9_]+)\s*\(f\s*:\s*SyncImpl\)\s*:\s*Prop", before, flags=re.M)
    result.update(verdict="accept", stage="done", laws=[l for l in laws if l != "Passes"])
    return result


def check_mode(mode: str, paranoid: bool) -> dict:
    if mode == "laws":
        return check_laws()
    module, config = MODES[mode]
    result: dict = {"mode": mode, "verdict": "reject", "stage": "", "problems": []}
    if not (ROOT / f"{module}.lean").exists():
        result.update(stage="absent_file", problems=[f"{module}.lean does not exist"])
        return result
    code, out = run(["lake", "build", module])
    if code != 0:
        result.update(stage="build", problems=[f"{module}.lean does not build"], output=clean(out))
        return result
    cfg = json.loads((ROOT / config).read_text(encoding="utf-8"))
    names = cfg["theorem_names"] + cfg["definition_names"]
    probe = ROOT / ".lake" / f"{mode}_names.lean"
    probe.write_text(f"import {module}\n" + "".join(f"#check @{n}\n" for n in names), encoding="utf-8")
    _, out = run(["lake", "env", "lean", str(probe)])
    absent = [n for n in names if f"Unknown identifier `{n}`" in out]
    if absent:
        result.update(stage="absent_name", problems=[f"{module}.lean does not declare {n}" for n in absent])
        return result
    cmd = ["lake", "comparator", "--config", config]
    if paranoid:
        cmd.append("--paranoid")
    if shutil.which("bwrap") is None:
        cmd.append("--inadvisably-no-sandbox")
    code, out = run(cmd)
    if code != 0:
        result.update(stage="comparator", problems=[f"exit code {code}"], output=clean(out))
        return result
    result.update(verdict="accept", stage="done")
    if mode == "gap":
        _, out = run(["lake", "env", "lean", "--run", "SyncGapRunner.lean"])
        result["question"] = [l for l in out.splitlines() if l.strip()]
    return result


def main() -> int:
    args = sys.argv[1:]
    modes = [a for a in args[1:] if a in ("laws", "gap", "complete")]
    if not args or args[0] != "check" or not modes:
        print(__doc__)
        return 2
    actor = args[args.index("--actor") + 1] if "--actor" in args else "agent"
    started = time.time()
    results = [check_mode(mode, "--paranoid" in args) for mode in modes]
    accepted = [r for r in results if r["verdict"] == "accept"]
    present = [r for r in results if r["stage"] != "absent_file"]
    report = {
        "experiment": "exp12-agent-written-laws-sync",
        "verdict": "accept" if accepted else "reject",
        "accepted_mode": accepted[0]["mode"] if accepted else None,
        "results": present if present else results,
        "seconds": round(time.time() - started, 2),
    }
    print(json.dumps(report, indent=2))
    with (ROOT / RUN_LOG).open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "actor": actor, "modes": modes,
                             "verdict": report["verdict"], "mode": report["accepted_mode"],
                             "seconds": report["seconds"]}) + "\n")
    return 0 if accepted else 1


if __name__ == "__main__":
    sys.exit(main())
