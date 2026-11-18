#!/usr/bin/env python3
"""Hard Proof v2, experiment 16: a review loop "until dry" on an agent-written law set.

Each round:
  1. A reviewer worker (no proof duty, with a shell) says "gap" or "complete". For a gap it names one input.
  2. The answer to that input is what the shipped code does (the same stand-in for the human as in experiment 12).
  3. A law-author worker adds a law for the answer, or says that no law is necessary.
The loop stops when two reviews in sequence say "complete", or at the round limit.

After the loop, the proof loop of experiment 12 starts from the final laws (`loop12.py`). Its first round is the
certified check of the end state: a completeness proof means that the review loop ended correctly.

Usage:
    python3 reviewloop.py --start a_haiku --base base --name rl_a_haiku [--max-rounds 8]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXP12 = HERE.parent / "exp12"
WORK = Path.home() / "Projects" / "hp-work" / "rl"

REVIEW_FILES = ["Sync.lean", "DESCRIPTION.md", "lakefile.toml", "lean-toolchain", "lake-manifest.json", ".gitignore"]
REVIEW_TOOLS = {"allowed_tools": ["Read", "Glob", "Grep", "Write", "Edit", "Bash(cd:*)", "Bash(ls:*)", "Bash(pwd)", "Bash(cat:*)",
                                  "Bash(lake:*)", "Bash(lean:*)", "Bash(python3:*)", "Bash(grep:*)", "Bash(wc:*)", "Bash(head:*)",
                                  "Bash(tail:*)", "Bash(sed -n:*)", "Bash(mkdir:*)"],
                "disallowed_tools": ["WebFetch", "WebSearch", "Task", "Agent", "NotebookEdit"]}

REVIEW_TASK = (
    "Context: this Lean 4 project models a real command, `puppetmaster models sync`: it adds to a model registry the starter entries that the registry lacks. `Sync.lean` has the model. A `SyncImpl` is a design of the command: it takes the settings, the starter list and the registry, and returns the new registry. `DESCRIPTION.md` has the sentences of the command's own documentation. `SyncLaws.lean` has laws that an agent wrote from that description. The owner believes that these laws describe the command completely.\n\n"
    "Your role: you are the reviewer. Test that belief. One of two results is true, and you must find out which one:\n\n"
    "1. A gap exists. Two designs each pass every law (`Sync.Passes`), but they give different registries for one legal input (a legal input has a starter list with `DistinctIds`).\n\n"
    "2. No gap exists. Each two designs that pass every law give the same registry for each legal input.\n\n"
    "You do not need to write a proof, and no proof checker reads your answer.\n\n"
    "Your work: write the file `answer.json` in this folder. It is one JSON object with this shape:\n\n"
    '{"verdict": "gap" or "complete", "open_decision": "one sentence: the decision that the laws leave open", '
    '"input": {"enable": true or false, "locked_adapters": [adapter numbers], "starter": [[id, adapter, model, enabled 0 or 1], ...], "registry": [[id, adapter, model, enabled 0 or 1], ...]}, '
    '"result_a": "the registry that the first design gives", "result_b": "the registry that the second design gives", "reason": "one or two sentences"}\n\n'
    "For verdict \"complete\", leave out `open_decision`, `input`, `result_a` and `result_b`.\n\n"
    "Rules:\n- Write `answer.json` only. Do not change another file.\n"
    "- You can run `lake`, `lean` and `python3` for analysis. If you write a script or a Lean file, put it in `.lake/` (git ignores that folder).\n"
    "- Stay in this folder. Do not read a file outside this folder.\n"
    "- Give your best answer. `verdict` must be \"gap\" or \"complete\".\n\n"
    "Report: say in plain words which result is true and why.")
REVIEW_CHECK = "python3 -c \"import json;d=json.load(open('answer.json'));assert d['verdict'] in ('gap','complete');assert d['verdict']=='complete' or isinstance(d['input']['starter'],list)\""


def show_rows(rows) -> str:
    return "; ".join(f"id {i} (adapter {a}, model {m}, {'enabled' if e else 'disabled'})" for i, a, m, e in rows)


def code_answer(base: Path, inp: dict) -> list:
    rows = lambda rs: ";".join(",".join(str(int(x)) for x in r) for r in rs)
    line = f"{1 if inp.get('enable') else 0}|{','.join(str(int(a)) for a in inp.get('locked_adapters') or [])}|{rows(inp.get('starter') or [])}|{rows(inp.get('registry') or [])}\n"
    p = subprocess.run(["lake", "env", "lean", "--run", "SyncRunner.lean"], cwd=base, input=line, capture_output=True, text=True)
    out = p.stdout.strip().splitlines()[0] if p.stdout.strip() else ""
    return [[int(x) for x in r.split(",")] for r in out.split(";") if r]


def law_task(inp: dict, answer: dict, shown: str) -> str:
    q = (f"    input: enable_flag={str(bool(inp.get('enable'))).lower()} locked_adapters={inp.get('locked_adapters') or []}\n"
         f"    input: starter=[{show_rows(inp.get('starter') or [])}]\n"
         f"    input: registry=[{show_rows(inp.get('registry') or [])}]\n"
         f"    design A result: {answer.get('result_a')}\n"
         f"    design B result: {answer.get('result_b')}")
    return (
        "Context: this Lean 4 project models a real command, `puppetmaster models sync`. `SyncLaws.lean` has the laws for this command. A reviewer reports that the laws leave one behavior open. The report has no proof. The reviewer says that two designs pass every law and give different registries for this legal input:\n\n"
        f"{q}\n\n"
        f"The reviewer names the open decision like this: {answer.get('open_decision')}\n\n"
        f"The owner looked at this case and answered: the correct result for this input is [{shown}].\n\n"
        "Your work: add to `SyncLaws.lean` the law that this answer shows was absent. Write a general law for the requirement behind the answer, not a law for this one input only. Then add the new law to `Passes`, and keep `ref_passes` and `some_design_fails` proved. If the laws in the file already force this result, a new law is not necessary: change nothing and say so in your report.\n\n"
        "The gate is `python3 gate12.py check laws`. It prints a JSON report. Verdict `accept` is the only success.\n\n"
        "Rules:\n- Edit `SyncLaws.lean` only.\n- Do not change or remove a law that is in the file. Add to the file.\n- The new law must be true for the shipped code (`ref`). It says what a user of the command can observe. It must not mention `ref` or `adjust`, and it must not copy their code.\n- Do not add a law that the answer does not support.\n- Do not use `sorry`, a new `axiom`, or `native_decide`.\n- The toolchain is Lean 4.36.0 with no Mathlib.\n\n"
        "Report: the new law in plain words, or the reason why no law is necessary.")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", required=True)
    parser.add_argument("--base", default="base")
    parser.add_argument("--name", required=True)
    parser.add_argument("--model", default="claude-sonnet-5-5")
    parser.add_argument("--max-rounds", type=int, default=8)
    parser.add_argument("--dry", type=int, default=2, help="reviews in sequence that say complete")
    args = parser.parse_args()
    os.environ["HP_BASE"] = args.base
    sys.path.insert(0, str(EXP12))
    import loop12  # noqa: E402  (reads HP_BASE at import)

    base = EXP12 / args.base
    laws_text = (EXP12 / args.start / "SyncLaws.lean").read_text(encoding="utf-8")
    result: dict = {"name": args.name, "start": args.start, "base": args.base, "model": args.model,
                    "first_laws": loop12.law_names(laws_text), "rounds": [], "outcome": "round limit"}
    dry, n = 0, 0
    while n < args.max_rounds:
        n += 1
        rid = hashlib.sha256(f"hp16|{args.name}|{n}".encode()).hexdigest()[:10]
        folder = WORK / rid
        if folder.exists():
            shutil.rmtree(folder)
        folder.mkdir(parents=True)
        for f in REVIEW_FILES:
            shutil.copy(base / f, folder / f)
        (folder / "SyncLaws.lean").write_text(laws_text, encoding="utf-8")
        g = loop12.graph(f"hp16-{rid}", args.model, ["answer.json"], REVIEW_TASK, REVIEW_CHECK)
        g["nodes"][0]["payload"] = REVIEW_TOOLS
        flow = loop12.run_flow(folder, g)
        entry: dict = {"round": n, "review_folder": rid, "review": flow, "laws": loop12.law_names(laws_text)}
        try:
            answer = json.loads((folder / "answer.json").read_text())
        except Exception:
            entry["note"] = "no answer file"
            result["rounds"].append(entry)
            result["outcome"] = "reviewer failed"
            break
        entry["verdict"] = answer.get("verdict")
        entry["answer"] = answer
        if answer.get("verdict") == "complete":
            dry += 1
            result["rounds"].append(entry)
            if dry >= args.dry:
                result["outcome"] = "reviewer says complete"
                break
            continue
        dry = 0
        inp = answer["input"]
        code_rows = code_answer(base, inp)
        shown = show_rows(code_rows)
        entry["code_result"] = shown
        law = WORK / f"{rid}-law"
        if law.exists():
            shutil.rmtree(law)
        law.mkdir()
        for f in loop12.LAW_HUMAN:
            shutil.copy(base / f, law / f)
        shutil.copy(base / ".gitignore", law / ".gitignore")
        shutil.copy(base / "lake-manifest.json", law / "lake-manifest.json")
        (law / "SyncLaws.lean").write_text(laws_text, encoding="utf-8")
        check = (f"printf '%s  %s\\n' {loop12.pins(law, loop12.LAW_HUMAN)} "
                 "| shasum -a 256 -c - && python3 gate12.py check laws --actor flow")
        flow = loop12.run_flow(law, loop12.graph(f"hp16-{rid}-law", args.model, ["SyncLaws.lean"], law_task(inp, answer, shown), check))
        _, out = loop12.sh([sys.executable, "gate12.py", "check", "laws", "--actor", "pilot-verify"], law)
        try:
            law_report = loop12.parse_json(out)
        except Exception:
            law_report = {"verdict": "error"}
        new_text = (law / "SyncLaws.lean").read_text(encoding="utf-8")
        old_defs, new_defs = loop12.law_defs(laws_text), loop12.law_defs(new_text)
        kept = all(new_defs.get(k) == v for k, v in old_defs.items())
        added = [k for k in new_defs if k not in old_defs]
        entry.update(law_author=flow, law_gate=law_report.get("verdict"), old_laws_unchanged=kept,
                     new_laws={k: new_defs[k] for k in added})
        result["rounds"].append(entry)
        if law_report.get("verdict") == "accept" and kept and added:
            laws_text = new_text
    result["final_laws"] = loop12.law_names(laws_text)
    result["reviews"] = len(result["rounds"])
    result["questions"] = sum(1 for r in result["rounds"] if r.get("verdict") == "gap")
    result["laws_added"] = sum(len(r.get("new_laws") or {}) for r in result["rounds"])
    cost = sum((r["review"].get("cost_usd") or 0) + ((r.get("law_author") or {}).get("cost_usd") or 0) for r in result["rounds"])
    secs = sum((r["review"].get("seconds") or 0) + ((r.get("law_author") or {}).get("seconds") or 0) for r in result["rounds"])
    result["cost_usd"], result["seconds"] = round(cost, 2), secs
    out_dir = HERE / "reviewloop"
    out_dir.mkdir(exist_ok=True)
    final = EXP12 / f"{args.name}_final"
    if final.exists():
        shutil.rmtree(final)
    final.mkdir()
    (final / "SyncLaws.lean").write_text(laws_text, encoding="utf-8")
    (out_dir / f"{args.name}.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
    # The certified check of the end state, and the proof loop from there.
    p = subprocess.run([sys.executable, "loop12.py", "--start", f"{args.name}_final", "--name", f"{args.name}_finish"],
                       cwd=EXP12, capture_output=True, text=True, env={**os.environ, "HP_BASE": args.base})
    try:
        fin = json.loads((EXP12 / f"{args.name}_finish" / "result.json").read_text())
        result["end_state_complete"] = fin["outcome"] == "complete" and fin["questions"] == 0
        result["finish"] = {"outcome": fin["outcome"], "questions": fin["questions"], "final_laws": fin["final_laws"],
                            "cost_usd": round(sum((x["adversary"]["cost_usd"] or 0) + ((x.get("law_author") or {}).get("cost_usd") or 0) for x in fin["rounds"]), 2),
                            "seconds": sum((x["adversary"]["seconds"] or 0) + ((x.get("law_author") or {}).get("seconds") or 0) for x in fin["rounds"]),
                            "questions_text": [x.get("question") for x in fin["rounds"] if x.get("question")]}
    except Exception as exc:
        result["finish"] = {"error": str(exc), "log": (p.stdout + p.stderr)[-500:]}
    (out_dir / f"{args.name}.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({k: result.get(k) for k in ("name", "outcome", "reviews", "questions", "laws_added", "cost_usd", "seconds",
                                                 "end_state_complete", "finish")}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
