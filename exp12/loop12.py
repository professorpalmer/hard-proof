#!/usr/bin/env python3
"""Hard Proof, experiment 12: run the full loop on one agent-written law set.

Each round:
  1. An adversary worker must supply a gap certificate or a completeness proof.
  2. For a gap, the gate prints one question. The answer is what the shipped
     code does for that case. (A stand-in for the human gives this answer.)
  3. A law-author worker adds a general law for the answer. The gate checks that
     the shipped-code mirror still passes each law and that each old law is unchanged.
The loop stops when the gate accepts a completeness proof.

Usage:
    python3 loop12.py --start a_haiku --name loop_haiku [--model claude-sonnet-5-5] [--max-rounds 6]
"""
from __future__ import annotations

import argparse
import os
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE / os.environ.get("HP_BASE", "base")
HUMAN = ["Sync.lean", "DESCRIPTION.md", "gate12.py", "lakefile.toml", "lean-toolchain",
         "SyncGapChallenge.lean", "SyncCompleteChallenge.lean", "SyncGapRunner.lean",
         "comparator_gap.json", "comparator_complete.json"]
LAW_HUMAN = ["Sync.lean", "DESCRIPTION.md", "gate12.py", "lakefile.toml", "lean-toolchain"]
TOOLS = ["Bash(cd:*)", "Bash(ls:*)", "Bash(pwd)", "Bash(cat:*)", "Bash(git status:*)", "Bash(git diff:*)",
         "Bash(git log:*)", "Bash(lake:*)", "Bash(lean:*)", "Bash(python3 gate12.py:*)", "Bash(shasum:*)"]

ADVERSARY_TASK = (
    "Context: this Lean 4 project models a real command, `puppetmaster models sync`: it adds to a model registry the starter entries that the registry lacks. `Sync.lean` has the model. A `SyncImpl` is a design of the command: it takes the settings, the starter list and the registry, and returns the new registry. `DESCRIPTION.md` has the sentences of the command's own documentation. `SyncLaws.lean` has laws that an agent wrote from that description. The owner believes that these laws describe the command completely.\n\n"
    "Your role: you are the adversary. Test that belief. One of two results is true, and you must find out which one:\n\n"
    "1. A gap exists. Two designs each pass every law (`Sync.Passes`), but they give different registries for one legal input. To show this, write `SyncGapSolution.lean` (read `SyncGapChallenge.lean`): `namespace SyncGap` with `designA`, `designB`, `config`, `starter`, `registry`, and complete proofs of `a_passes`, `b_passes`, `starter_distinct`, and `differ`.\n\n"
    "2. No gap exists. Each two designs that pass every law give the same registry for each legal input. To show this, write `SyncCompleteSolution.lean` (read `SyncCompleteChallenge.lean`): `namespace SyncComplete` with a complete proof of `laws_complete`.\n\n"
    "Each statement must be the same as the statement in the challenge file. The gate is `python3 gate12.py check gap complete`. It prints a JSON report and accepts one correct result of either kind. Verdict `accept` is the only success.\n\n"
    "Rules:\n- Edit `SyncGapSolution.lean` and `SyncCompleteSolution.lean` only. The gate rejects the run if another file changes.\n- Do not use `sorry`, a new `axiom`, or `native_decide`.\n- The toolchain is Lean 4.36.0 with no Mathlib. `lake build SyncGapSolution` or `lake build SyncCompleteSolution` gives the compiler errors.\n- If you cannot complete either result, report how far you got, and end your reply with `VERDICT: FAIL - <reason>`.\n\n"
    "Report: say in plain words which result is true and why.")

FIRST_TASK = (
    "Context: this Lean 4 project models a real command, `puppetmaster models sync`: it adds to a model registry the starter entries that the registry lacks. `Sync.lean` has the model. A `SyncImpl` is a design of the command: it takes the settings, the starter list and the registry, and returns the new registry. `ref` is a mirror of the shipped code. `DESCRIPTION.md` has the sentences of the command's own documentation.\n\n"
    "Your work: write the laws for this command from `DESCRIPTION.md`. Write `SyncLaws.lean`:\n"
    "- Start with `import Sync` and use `namespace Sync`.\n"
    "- For each requirement that the description states, write one law `def <Name> (f : SyncImpl) : Prop := ...`, with a doc comment that quotes the sentence it comes from.\n"
    "- Write `def Passes (f : SyncImpl) : Prop` as the conjunction of your laws.\n"
    "- Prove `theorem ref_passes : Passes ref`: the shipped code obeys each law.\n"
    "- Prove `theorem some_design_fails : ∃ f : SyncImpl, ¬ Passes f`: the laws reject some design.\n\n"
    "The gate is `python3 gate12.py check laws`. It prints a JSON report. Verdict `accept` is the only success.\n\n"
    "Rules:\n- Edit `SyncLaws.lean` only. The gate rejects the run if another file changes.\n"
    "- A law must state a requirement of the description. Do not write a law for behavior that the description does not state. If the description is silent or not clear for some case, do not invent a law for it. Name that case in your report.\n"
    "- A law says what a user of the command can observe. It must not mention `ref` or `adjust`, and it must not copy their code. The gate rejects these two names in the text before `theorem ref_passes`.\n"
    "- A law can assume a legal starter list (`DistinctIds st`).\n"
    "- Do not use `sorry`, a new `axiom`, or `native_decide`.\n"
    "- The toolchain is Lean 4.36.0 with no Mathlib. `lake build SyncLaws` gives the compiler errors.\n"
    "- If a law that the description states is false for `ref`, stop. Report the law and the case, and end your reply with `VERDICT: FAIL - <reason>`.\n\n"
    "Report: list each law with its sentence, and list each case where the description is silent or not clear.")


def law_task(question: list[str], answer: str) -> str:
    q = "\n".join("    " + l for l in question if not l.startswith("shipped code:"))
    return (
        "Context: this Lean 4 project models a real command, `puppetmaster models sync`. `SyncLaws.lean` has the laws for this command. An adversary proved that the laws leave one behavior open. Two designs pass every law and give different registries for this legal input:\n\n"
        f"{q}\n\n"
        f"The owner looked at this case and answered: the correct result for this input is {answer}.\n\n"
        "Your work: add to `SyncLaws.lean` the law that this answer shows was absent. Write a general law for the requirement behind the answer, not a law for this one input only. Then add the new law to `Passes`, and keep `ref_passes` and `some_design_fails` proved.\n\n"
        "The gate is `python3 gate12.py check laws`. It prints a JSON report. Verdict `accept` is the only success.\n\n"
        "Rules:\n- Edit `SyncLaws.lean` only.\n- Do not change or remove a law that is in the file. Add to the file.\n- The new law must be true for the shipped code (`ref`). It says what a user of the command can observe. It must not mention `ref` or `adjust`, and it must not copy their code.\n- Do not add a law that the answer does not support.\n- Do not use `sorry`, a new `axiom`, or `native_decide`.\n- The toolchain is Lean 4.36.0 with no Mathlib.\n\n"
        "Report: the new law in plain words.")


def sh(cmd: list[str], cwd: Path, timeout: int | None = None) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return proc.returncode, proc.stdout + proc.stderr


def parse_json(text: str) -> dict:
    return json.loads(text[text.find("{"): text.rfind("}") + 1])


def pins(folder: Path, files: list[str]) -> str:
    return " ".join(f"{hashlib.sha256((folder / f).read_bytes()).hexdigest()} {f}" for f in files)


def run_flow(folder: Path, graph: dict) -> dict:
    sh(["git", "init", "-q"], folder)
    sh(["git", "add", "-A"], folder)
    sh(["git", "commit", "-q", "-m", "round baseline"], folder)
    gpath = folder / ".lake" / "graph.json"
    gpath.parent.mkdir(exist_ok=True)
    gpath.write_text(json.dumps(graph, indent=1), encoding="utf-8")
    _, out = sh(["puppetmaster", "flow", "run", str(gpath)], folder)
    run_id = parse_json(out)["run_id"]
    _, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", "3600"], folder, timeout=4000)
    flow = parse_json(out)
    visits = [s for s in flow.get("steps", []) if s.get("node") == "prove"]
    seconds, cost = 0.0, 0.0
    for s in visits:
        for job in s.get("job_ids") or []:
            _, st = sh(["puppetmaster", "status", job], folder)
            try:
                j = json.loads(st)["job"]
                seconds += (datetime.fromisoformat(j["completed_at"]) - datetime.fromisoformat(j["created_at"])).total_seconds()
            except Exception:
                pass
            _, art = sh(["puppetmaster", "artifacts", job], folder)
            found = re.findall(r'total_cost_usd\\?":\s*([0-9.]+)', art)
            cost += float(found[-1]) if found else 0.0
    return {"flow": run_id, "status": flow.get("status"), "visits": len(visits),
            "verdicts": [s.get("verdict") for s in visits], "seconds": round(seconds), "cost_usd": round(cost, 2)}


def graph(name: str, model: str, files: list[str], task: str, check: str) -> dict:
    return {"id": name, "entry": "prove",
            "defaults": {"adapter": "claude-code", "model": model, "timeout_seconds": 3000, "finish": "criteria"},
            "nodes": [{"id": "prove", "kind": "agent", "role": "code", "files": files, "task": task,
                       "payload": {"allowed_tools": TOOLS}},
                      {"id": "gate", "kind": "shell", "command": check},
                      {"id": "done", "kind": "end", "status": "pass"},
                      {"id": "objected", "kind": "end", "status": "fail"},
                      {"id": "failed", "kind": "end", "status": "fail"}],
            "edges": [{"from": "prove", "to": "objected", "when": "FAIL"},
                      {"from": "prove", "to": "gate", "when": "ok"},
                      {"from": "gate", "to": "done", "when": "ok"},
                      {"from": "gate", "to": "prove", "when": "fail", "max": 3},
                      {"from": "gate", "to": "failed", "when": "fail"},
                      {"from": "prove", "to": "failed"}]}


def law_names(text: str) -> list[str]:
    return [n for n in re.findall(r"^\s*def\s+([A-Za-z0-9_]+)\s*\(f\s*:\s*SyncImpl\)\s*:\s*Prop", text, flags=re.M) if n != "Passes"]


def law_defs(text: str) -> dict[str, str]:
    """Each law name with its definition text, white space collapsed."""
    out = {}
    for m in re.finditer(r"def\s+([A-Za-z0-9_]+)\s*\(f\s*:\s*SyncImpl\)\s*:\s*Prop\s*:=(.*?)(?=\n\s*\n|\n/--|\ntheorem|\ndef|\Z)", text, flags=re.S):
        if m.group(1) != "Passes":
            out[m.group(1)] = " ".join(m.group(2).split())
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", required=True, help="folder with the first SyncLaws.lean")
    parser.add_argument("--name", required=True)
    parser.add_argument("--model", default="claude-sonnet-5-5")
    parser.add_argument("--max-rounds", type=int, default=8)
    args = parser.parse_args()
    root = HERE / args.name
    if root.exists():
        shutil.rmtree(root)
    root.mkdir()
    laws_text = (HERE / args.start / "SyncLaws.lean").read_text(encoding="utf-8")
    result: dict = {"start": args.start, "model": args.model, "first_laws": law_names(laws_text),
                    "rounds": [], "outcome": "max rounds reached"}
    for rnd in range(1, args.max_rounds + 1):
        # 1. adversary
        adv = root / f"round{rnd}_adversary"
        adv.mkdir()
        for f in HUMAN:
            shutil.copy(BASE / f, adv / f)
        shutil.copy(BASE / ".gitignore", adv / ".gitignore")
        shutil.copy(BASE / "lake-manifest.json", adv / "lake-manifest.json")
        (adv / "SyncLaws.lean").write_text(laws_text, encoding="utf-8")
        check = (f"printf '%s  %s\\n' {pins(adv, HUMAN + ['SyncLaws.lean'])} | shasum -a 256 -c - "
                 "&& python3 gate12.py check gap complete --actor flow")
        flow = run_flow(adv, graph(f"hardproof-exp12-{args.name.replace('_', '-')}-adv{rnd}", args.model,
                                   ["SyncGapSolution.lean", "SyncCompleteSolution.lean"], ADVERSARY_TASK, check))
        _, out = sh([sys.executable, "gate12.py", "check", "gap", "complete", "--paranoid", "--actor", "pilot-verify"], adv)
        report = parse_json(out)
        entry: dict = {"round": rnd, "adversary": flow, "pilot_gate": report.get("verdict"),
                       "mode": report.get("accepted_mode"), "laws": law_names(laws_text)}
        if report.get("verdict") != "accept":
            entry["note"] = "the adversary result was not accepted"
            result["rounds"].append(entry)
            result["outcome"] = "adversary failed"
            break
        if report["accepted_mode"] == "complete":
            result["rounds"].append(entry)
            result["outcome"] = "complete"
            break
        question = next(r for r in report["results"] if r["mode"] == "gap")["question"]
        answer = next(l for l in question if l.startswith("shipped code:")).split(":", 1)[1].strip()
        entry.update(question=question, answer=answer)
        # 2. and 3. the answer becomes a law
        law = root / f"round{rnd}_law"
        law.mkdir()
        for f in LAW_HUMAN:
            shutil.copy(BASE / f, law / f)
        shutil.copy(BASE / ".gitignore", law / ".gitignore")
        shutil.copy(BASE / "lake-manifest.json", law / "lake-manifest.json")
        (law / "SyncLaws.lean").write_text(laws_text, encoding="utf-8")
        check = (f"printf '%s  %s\\n' {pins(law, LAW_HUMAN)} "
                 "| shasum -a 256 -c - && python3 gate12.py check laws --actor flow")
        flow = run_flow(law, graph(f"hardproof-exp12-{args.name.replace('_', '-')}-law{rnd}", args.model, ["SyncLaws.lean"],
                                   law_task(question, answer), check))
        _, out = sh([sys.executable, "gate12.py", "check", "laws", "--actor", "pilot-verify"], law)
        law_report = parse_json(out)
        new_text = (law / "SyncLaws.lean").read_text(encoding="utf-8")
        old_defs, new_defs = law_defs(laws_text), law_defs(new_text)
        kept = all(new_defs.get(k) == v for k, v in old_defs.items())
        added = [k for k in new_defs if k not in old_defs]
        entry["law_author"] = flow
        entry["law_gate"] = law_report.get("verdict")
        entry["old_laws_unchanged"] = kept
        entry["new_laws"] = {k: new_defs[k] for k in added}
        result["rounds"].append(entry)
        if law_report.get("verdict") != "accept" or not kept or not added:
            result["outcome"] = "law author failed"
            break
        laws_text = new_text
    result["final_laws"] = law_names(laws_text)
    result["questions"] = sum(1 for r in result["rounds"] if r.get("mode") == "gap")
    (root / "result.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
    (root / "SyncLaws.final.lean").write_text(laws_text, encoding="utf-8")
    print(json.dumps({"name": args.name, "outcome": result["outcome"], "questions": result["questions"],
                      "final_laws": result["final_laws"]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
