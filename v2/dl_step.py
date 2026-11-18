#!/usr/bin/env python3
"""Hard Proof v2, experiment 17: the shell steps of the one-flow proof loop.

    python3 dl_step.py gate STATE      after the adversary: pins, gate, then the question and the answer
    python3 dl_step.py lawgate STATE   after the law author: gate, old laws unchanged, one law added

The current folder is the run folder. STATE is a JSON file outside the run folder (pins, rounds, law snapshot).
Exit 1 sends the worker back. A last line `VERDICT: PASS` (complete) or `VERDICT: PARTIAL` (gap) routes the flow.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "exp12"))
os.environ.setdefault("HP_BASE", "base")
import loop12  # noqa: E402


def main() -> int:
    mode, state_path = sys.argv[1], Path(sys.argv[2])
    state = json.loads(state_path.read_text())
    cwd = Path.cwd()
    for name, sha in state["pins"].items():
        if hashlib.sha256((cwd / name).read_bytes()).hexdigest() != sha:
            print(f"REJECT: the file {name} changed. Restore it. You can edit your own files only.")
            return 1
    if mode == "gate":
        if hashlib.sha256((cwd / "SyncLaws.lean").read_bytes()).hexdigest() != state["laws_sha"]:
            print("REJECT: SyncLaws.lean changed. The adversary must not edit the laws. Restore it with `git checkout SyncLaws.lean` or from the text in the last law round.")
            return 1
        p = subprocess.run([sys.executable, "gate12.py", "check", "gap", "complete", "--actor", "flow"], capture_output=True, text=True)
        try:
            report = loop12.parse_json(p.stdout)
        except Exception:
            print("REJECT: the gate gave no report.\n" + p.stdout[-1500:] + p.stderr[-500:])
            return 1
        if report.get("verdict") != "accept":
            print("REJECT: the gate did not accept a result.\n" + json.dumps(report, indent=1)[:3500])
            return 1
        state["rounds"].append({"mode": report["accepted_mode"]})
        if report["accepted_mode"] == "complete":
            state_path.write_text(json.dumps(state, indent=1))
            print("The gate accepted a completeness proof. RESULT_COMPLETE")
            return 0
        question = next(r for r in report["results"] if r["mode"] == "gap")["question"]
        answer = next(l for l in question if l.startswith("shipped code:")).split(":", 1)[1].strip()
        shown = "\n".join("    " + l for l in question if not l.startswith("shipped code:"))
        n = sum(1 for r in state["rounds"] if r["mode"] == "gap")
        state["rounds"][-1].update(question=question, answer=answer)
        state["laws_before"] = (cwd / "SyncLaws.lean").read_text(encoding="utf-8")
        state_path.write_text(json.dumps(state, indent=1))
        (cwd / "ROUND.md").write_text(
            f"# Open case {n}\n\nAn adversary proved that the laws leave one behavior open. Two designs pass every law and give different registries for this legal input:\n\n"
            f"{shown}\n\nThe owner looked at this case and answered: the correct result for this input is {answer}.\n", encoding="utf-8")
        print(f"The gate accepted a gap certificate. ROUND.md has the open case {n} and the answer of the owner. RESULT_GAP")
        return 0
    if mode == "lawgate":
        p = subprocess.run([sys.executable, "gate12.py", "check", "laws", "--actor", "flow"], capture_output=True, text=True)
        try:
            report = loop12.parse_json(p.stdout)
        except Exception:
            print("REJECT: the gate gave no report.\n" + p.stdout[-1500:])
            return 1
        if report.get("verdict") != "accept":
            print("REJECT: the gate did not accept the laws.\n" + json.dumps(report, indent=1)[:3500])
            return 1
        new_text = (cwd / "SyncLaws.lean").read_text(encoding="utf-8")
        old, new = loop12.law_defs(state["laws_before"]), loop12.law_defs(new_text)
        if not all(new.get(k) == v for k, v in old.items()):
            print("REJECT: a law that was in the file changed. Do not change or remove an old law. Add to the file.")
            return 1
        added = [k for k in new if k not in old]
        if not added:
            print("REJECT: no new law is in SyncLaws.lean. Add the law for the case in ROUND.md.")
            return 1
        state["rounds"][-1]["new_laws"] = {k: new[k] for k in added}
        state["laws_sha"] = hashlib.sha256(new_text.encode("utf-8")).hexdigest()
        state_path.write_text(json.dumps(state, indent=1))
        for name in ("SyncGapSolution.lean", "SyncCompleteSolution.lean"):
            if (cwd / name).exists():
                (cwd / name).unlink()
        print(f"The gate accepted the laws. New law: {', '.join(added)}. The old solution files of the adversary were removed.")
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(main())
