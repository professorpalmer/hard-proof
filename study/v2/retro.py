#!/usr/bin/env python3
"""Hard Proof v2: the proof pipeline on real bugs, at the commit before each fix.

Stages for one bug (each stage is one worker in a folder with a hash for a name):
  M  model author   writes the Lean mirror of the function, the codec, the link adapter and the quoted documentation
  L  law author     writes laws from the quoted documentation; it does not have the mirror or the code
  R  ref prover     proves that the mirror passes each law, or gives a conflict certificate
  A  adversary      gives a gap certificate or a completeness proof
A conflict or a gap gives one concrete input. The stand-in for the human answers with the result of the code
AFTER the fix. The bug is detected when that result is different from the result of the code before the fix.

Usage:
    python3 retro.py run [--only ID ...] [--concurrency N] [--max-steps 6]
    python3 retro.py score
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import os

import guard
from bugs import PKG, SRC, WORK
from flowrun import run_agent

HERE = Path(__file__).resolve().parent
# The tool folder is beside the study folders in the working copy, and one level up in the public repository.
TOOL = next((p / "tool" for p in HERE.parents if (p / "tool" / "hpflow").is_dir()), HERE.parent / "tool")
HP = str(TOOL / "hp")
RUNS = WORK / "p"
OUT = HERE / "retro"
AUTHOR = ["Types.lean", "Ref.lean", "Codec.lean", "link_adapter.py", "DESCRIPTION.md", "hardproof.json"]
IGNORE = "hp/\n.lake/\n__pycache__/\n*.pyc\nhardproof_runs.jsonl\nhardproof.lock.json\n"
HP_TOOL = [f"Bash({HP}:*)", "Bash(rm:*)", "Bash(touch:*)", "Bash(timeout:*)"]

ORACLE = r'''
import sys, json
sys.path.insert(0, sys.argv[1])
from pathlib import Path
from hpflow.proof.domain import Domain
from hpflow.proof.checks import load_adapter
from hpflow.proof.link import load_function
d = Domain(Path(sys.argv[2]))
a = load_adapter(d)
try:
    m, f = load_function(d.config(), Path(sys.argv[3]))
    case = a.decode(sys.argv[4])
    print(json.dumps({"ok": True, "out": a.encode_result(a.call(f, case))}))
except BaseException as e:
    print(json.dumps({"ok": False, "out": type(e).__name__, "message": str(e)[:200]}))
'''

M_TASK = """The folder `project/` has the Python source of a tool. This folder is also a `hardproof` domain for one function of that tool: `{function}` in `project/{file}`. `HARDPROOF.md` explains the tool and the domain contract. Read it first.

Your work: write the author files of the domain, so that the Lean function `HP.ref` is an exact mirror of the Python function.

- `Types.lean`: `Input`, `Output`, `Impl`, `legal`, `Legal`, and the words that a law about this function needs (small helper definitions with clear names). No `ref` here.
- `Ref.lean`: `HP.ref`, the mirror of the Python code, with its helpers.
- `Codec.lean` and `link_adapter.py`: the text format of one input and one output, the case generator, and the call into the real function.
- `hardproof.json`: it is written. Correct the module or function name only if the import fails.
- `DESCRIPTION.md`: the documentation of the function as exact quotes. Use the docstring, the comments at the function, and sentences in `project/docs` and `project/README.md` that state what this function or its feature must do. Write each as a numbered line `N. "exact quote"` followed by a line `Source: project/<path>`. Then a section `## Model words` that maps each model word to the documentation word. Do not write a sentence of your own about what the function does or must do.

Rules:
- Mirror the code as it is. `ref` must give the result that the Python function gives, also where you think that the result is odd. Do not correct anything.
- Make `Input` cover as much of the real input space as you can model exactly. When the logic of the function depends on text, model the text (for example as a list of characters, or as a list of tokens with the properties that the code tests). When a part of the input space cannot be modeled, restrict `legal` and `gen` to the part that you model, and list what is left out below a heading `## Not in the model` in `DESCRIPTION.md`.
- `gen` must make varied inputs that reach each branch of the function, with edge cases (empty values, equal values, values at each limit that the code tests).
- If the function needs small state (a clock value, a dict, a list of files), make it a part of `Input` and build it in `call`.
- Standard library only. No network. Do not change `project/`.
- If the function is a method of a class, set `function` in `hardproof.json` to the name of the class, and call the method inside `call`.
- Put scratch files in `.lake/` (git ignores that folder). Do not leave other files in this folder.

Checks (run them, read the JSON reports):
- `{hp} check model`
- `{hp} link --repo project --cases 3000 --mutants 20` must give verdict `agree`. Look at the mutants that survive: when a mutant survives because `gen` does not reach a branch, make `gen` better.

If you cannot model the function in a way that keeps its logic, write the reason into `NOTES.md` and end your reply with `VERDICT: FAIL - <reason>`. Else end with `VERDICT: PASS`."""

L_TASK = """This folder is a `hardproof` domain for one function of a real tool. `HARDPROOF.md` explains the tool. `Types.lean` has the types of the function (`Input`, `Output`, `Impl := Input → Output`, `Legal`) and the words that a law can use. `DESCRIPTION.md` has the sentences of the documentation of the function. You do not have the code of the function.

Your work: write `Laws.lean` from `DESCRIPTION.md`.
- Start with `import Types` and use `namespace HP`. Import nothing else.
- For each requirement that the description states, write one law `def <Name> (f : Impl) : Prop := ...`, with a doc comment that quotes the sentence it comes from. A law says what a user of the function can observe: a relation between a legal input and the output.
- Write `def Passes (f : Impl) : Prop` as the conjunction of your laws.
- Prove `theorem some_design_fails : ∃ f : Impl, ¬ Passes f`.

The gate is `{hp} check laws`. It prints a JSON report. Verdict `accept` is the only success.

Rules:
- Edit `Laws.lean` only.
- A law must state a requirement of the description. Do not write a law for behavior that the description does not state. If the description is silent or not clear for some case, do not invent a law for it. Name that case in your report.
- Do not use `sorry`, a new `axiom`, or `native_decide`. The toolchain is Lean 4.36.0 with no Mathlib.

Report: list each law with its sentence, and each case where the description is silent or not clear. End with `VERDICT: PASS` when the gate accepts."""

R_TASK = """This folder is a `hardproof` domain for one function of a real tool. `HARDPROOF.md` explains the tool. `Ref.lean` has `HP.ref`, a mirror of the shipped code. A link test showed that it gives the same results as the real code. `Laws.lean` has laws that an agent wrote from the documentation (`DESCRIPTION.md`). That agent did not see the code.

One of two results is true, and you must find out which one:

1. The code obeys the laws. To show this, write `RefPassesSolution.lean`: `theorem HPRef.ref_passes : Passes ref`, with a complete proof.

2. The code breaks one law on a legal input. To show this, write `ConflictSolution.lean`: the first line is the comment `-- hardproof-law: <Law>` with the name of that one law, then `def HPConflict.input : Input`, `theorem HPConflict.input_legal : Legal input`, and `theorem HPConflict.ref_breaks : ¬ <Law> ref`. Select an `input` that shows the conflict.

The challenge files in `hp/` have the exact statements. The gate is `{hp} check ref conflict`. It prints a JSON report and accepts one correct result of either kind. Verdict `accept` is the only success.

Rules:
- Edit `RefPassesSolution.lean` and `ConflictSolution.lean` only.
- Do not use `sorry`, a new `axiom`, or `native_decide`. The toolchain is Lean 4.36.0 with no Mathlib.
- If you cannot complete either result, report how far you got, and end your reply with `VERDICT: FAIL - <reason>`.

Report: say in plain words which result is true and why. End with `VERDICT: PASS` when the gate accepts."""

A_TASK = """This folder is a `hardproof` domain for one function of a real tool. `HARDPROOF.md` explains the tool. `Types.lean` has the types. `Laws.lean` has laws that an agent wrote from the documentation (`DESCRIPTION.md`). The owner believes that these laws describe the function completely.

Your role: you are the adversary. Test that belief. One of two results is true, and you must find out which one:

1. A gap exists. Two designs each pass every law (`Passes`), but they give different outputs for one legal input. To show this, write `GapSolution.lean`: `def HPGap.designA : Impl`, `def HPGap.designB : Impl`, `def HPGap.input : Input`, and complete proofs of `HPGap.a_passes`, `HPGap.b_passes`, `HPGap.input_legal` and `HPGap.differ`. The designs must be computable functions, because a runner evaluates them on the input.

2. No gap exists. Each two designs that pass every law give the same output for each legal input. To show this, write `CompleteSolution.lean`: a complete proof of `HPComplete.laws_complete`.

The challenge files in `hp/` have the exact statements. The gate is `{hp} check gap complete`. It prints a JSON report and accepts one correct result of either kind. Verdict `accept` is the only success.

Rules:
- Edit `GapSolution.lean` and `CompleteSolution.lean` only.
- Do not use `sorry`, a new `axiom`, or `native_decide`. The toolchain is Lean 4.36.0 with no Mathlib.
- If you cannot complete either result, report how far you got, and end your reply with `VERDICT: FAIL - <reason>`.

Report: say in plain words which result is true and why. End with `VERDICT: PASS` when the gate accepts."""

LAW_ADD = """This folder is a `hardproof` domain for one function of a real tool. `Laws.lean` has the laws for this function. An adversary proved that the laws leave one behavior open. Two designs pass every law and give different outputs for this legal input:

    input: {shown}
    design A output: {a}
    design B output: {b}

The owner looked at this case and answered: the correct output for this input is `{answer}` (in the text format of `encodeOutput`).

Your work: add to `Laws.lean` the law that this answer shows was absent. Write a general law for the requirement behind the answer, not a law for this one input only. Add the new law to `Passes`, and keep `some_design_fails` proved.

The gate is `{hp} check laws`. Verdict `accept` is the only success.

Rules:
- Edit `Laws.lean` only. Do not change or remove a law that is in the file. Add to the file.
- Do not add a law that the answer does not support.
- Do not use `sorry`, a new `axiom`, or `native_decide`. The toolchain is Lean 4.36.0 with no Mathlib.

Report: the new law in plain words. End with `VERDICT: PASS` when the gate accepts."""

LAW_FIX = """This folder is a `hardproof` domain for one function of a real tool. `Laws.lean` has the laws for this function. A prover showed that the shipped code breaks the law `{law}` on this legal input:

    input: {shown}
    output of the shipped code: {ref}

The owner looked at this case and answered: the output of the shipped code is correct for this input. The law `{law}` is wrong or too strong.

Your work: correct the law `{law}` in `Laws.lean`, so that it permits this output and still states the requirement of its sentence in `DESCRIPTION.md` as far as the answer permits. If the sentence gives no requirement that is true for this case, remove the law from `Passes` and say so. Keep `some_design_fails` proved.

The gate is `{hp} check laws`. Verdict `accept` is the only success.

Rules:
- Edit `Laws.lean` only. Change the law `{law}` only.
- Do not use `sorry`, a new `axiom`, or `native_decide`. The toolchain is Lean 4.36.0 with no Mathlib.

Report: the corrected law in plain words. End with `VERDICT: PASS` when the gate accepts."""


def hp(folder: Path, *args: str, timeout: int = 1800) -> dict:
    try:
        # One pilot check at a time: a Lean kernel or a link test can use some GB of memory.
        with guard.locked("lean"):
            p = subprocess.run([HP, "--dir", str(folder), "--actor", "pilot", *args], capture_output=True, text=True, timeout=timeout,
                               env={**os.environ, "HARDPROOF_MAX_RSS_GB": "6"})
        t = p.stdout
        return json.loads(t[t.find("{"): t.rfind("}") + 1])
    except Exception as exc:
        return {"verdict": "error", "error": str(exc)[:200]}


def oracle(domain: Path, tree: Path, line: str) -> dict:
    try:
        p = subprocess.run([sys.executable, "-c", ORACLE, str(TOOL), str(domain), str(tree), line], capture_output=True,
                           text=True, timeout=120, cwd=tree)
        rows = [l for l in p.stdout.splitlines() if l.startswith("{")]
        return json.loads(rows[-1]) if rows else {"ok": False, "out": "no output", "message": p.stderr[-200:]}
    except subprocess.TimeoutExpired:
        return {"ok": False, "out": "timeout"}


def differ(line: str, a: dict, c: dict) -> bool:
    """The code before the fix and the code after the fix give different results for this input.
    No input, or a side that could not load the function, is not a difference."""
    if not line:
        return False
    if any((not x.get("ok")) and x.get("out") in ("DomainError", "ImportError", "AttributeError", "ModuleNotFoundError", "no output", "timeout") for x in (a, c)):
        return False
    return (a.get("ok"), a.get("out")) != (c.get("ok"), c.get("out"))


def sid(bug: str, stage: str) -> str:
    return hashlib.sha256(f"hp2p|{bug}|{stage}".encode()).hexdigest()[:10]


def fresh(bug: str, stage: str) -> Path:
    folder = RUNS / sid(bug, stage)
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir(parents=True)
    (folder / ".gitignore").write_text(IGNORE, encoding="utf-8")
    shutil.copy(TOOL / "README.md", folder / "HARDPROOF.md")
    return folder


def copy_files(src: Path, dst: Path, names: list[str]) -> None:
    for n in names:
        if (src / n).exists():
            shutil.copy(src / n, dst / n)


def quotes_ok(folder: Path) -> dict:
    """Each quoted sentence of DESCRIPTION.md must be text of a file in `project/`."""
    text = (folder / "DESCRIPTION.md").read_text(encoding="utf-8", errors="replace") if (folder / "DESCRIPTION.md").exists() else ""
    head = text.split("## Model words")[0]
    quotes = re.findall(r'^\s*\d+\.\s*"(.+?)"\s*$', head, flags=re.M | re.S)
    norm = lambda s: re.sub(r"[\s`*#>\\]+", " ", s).strip().lower()
    corpus = ""
    for p in (folder / "project").rglob("*"):
        if p.is_file() and p.suffix in (".py", ".md", ".txt", ".json", ".toml"):
            try:
                corpus += norm(p.read_text(encoding="utf-8", errors="replace")) + "\n"
            except Exception:
                pass
    missing = [q[:80] for q in quotes if norm(q) not in corpus]
    return {"quotes": len(quotes), "not_found": missing}


def stage(bug: dict, name: str, folder: Path, task: str, files: list[str], check: str, model: str, log: list) -> dict:
    r = run_agent(folder, f"hp2-{folder.name}", task.replace("{hp}", HP), files, model=model, shell=True, check=check,
                  repairs=2, timeout=3600, extra_allowed=HP_TOOL)
    r["stage"] = name
    log.append(r)
    return r


def one(bug: dict, max_steps: int) -> dict:
    b = bug["id"]
    if (OUT / f"{b}.json").exists():
        # A second process can finish this bug after the list of open bugs was made. Do not run it again.
        return json.loads((OUT / f"{b}.json").read_text())
    pre, post = SRC / b / "pre", SRC / b / "post"
    log: list = []
    res: dict = {"bug": b, "title": bug["title"], "repo": bug["repo"], "function": bug["function"], "kind": bug["kind"],
                 "stages": log, "items": [], "outcome": None}

    def done(outcome: str) -> dict:
        res["outcome"] = outcome
        res["cost_usd"] = round(sum(s.get("cost_usd") or 0 for s in log), 2)
        res["seconds"] = sum(s.get("seconds") or 0 for s in log)
        OUT.mkdir(exist_ok=True)
        (OUT / f"{b}.json").write_text(json.dumps(res, indent=1) + "\n", encoding="utf-8")
        return res

    # M: the model.
    m = fresh(b, "M")
    shutil.copytree(pre, m / "project")
    module = bug["file"][:-3].replace("/", ".")
    fn = bug["function"].split(" ")[0].split("(")[0]
    subprocess.run([HP, "new", str(m / "_new"), "--name", f"f{b}", "--module", module, "--function", fn.split(".")[-1]],
                   capture_output=True, text=True)
    for p in (m / "_new").iterdir():
        if p.name != "Laws.lean":
            shutil.move(str(p), str(m / p.name))
    shutil.rmtree(m / "_new", ignore_errors=True)
    check = f"{HP} check model >/dev/null && {HP} link --repo project --cases 2000 --mutants 0 >/dev/null"
    stage(bug, "M", m, M_TASK.format(function=bug["function"], file=bug["file"], hp=HP), AUTHOR + ["NOTES.md"], check, "opus", log)
    model_rep = hp(m, "check", "model")
    link_pre = hp(m, "link", "--repo", str(pre), "--cases", "5000", "--mutants", "20")
    res["model"] = {"check": model_rep.get("verdict"), "link_pre": link_pre.get("verdict"),
                    "mutants": link_pre.get("mutants"), "quotes": quotes_ok(m),
                    "not_in_model": "## Not in the model" in ((m / "DESCRIPTION.md").read_text(errors="replace") if (m / "DESCRIPTION.md").exists() else "")}
    if model_rep.get("verdict") != "accept" or link_pre.get("verdict") != "agree":
        return done("no model")
    link_post = hp(m, "link", "--repo", str(post), "--cases", "20000", "--mutants", "0")
    res["model"]["bug_in_model_scope"] = link_post.get("verdict") == "disagree" or bool(link_post.get("differences"))
    if link_post.get("verdict") not in ("agree", "disagree"):
        return done("the function is absent after the fix")
    res["model"]["link_post"] = {k: link_post.get(k) for k in ("verdict", "differences", "first_difference")}

    # L: the laws, with no view of the mirror.
    l = fresh(b, "L0")
    copy_files(m, l, ["Types.lean", "DESCRIPTION.md", "hardproof.json"])
    stage(bug, "L", l, L_TASK, ["Laws.lean"], f"{HP} check laws >/dev/null", "sonnet", log)
    rep = hp(l, "check", "laws")
    if rep.get("verdict") != "accept":
        return done("no laws")
    laws = (l / "Laws.lean").read_text(encoding="utf-8")
    res["first_laws"] = next((r.get("laws") for r in rep.get("results", []) if r.get("laws")), None)

    def domain(tag: str) -> Path:
        d = fresh(b, tag)
        copy_files(m, d, AUTHOR)
        (d / "Laws.lean").write_text(laws, encoding="utf-8")
        return d

    def law_round(tag: str, task: str) -> bool:
        nonlocal laws
        d = fresh(b, tag)
        copy_files(m, d, ["Types.lean", "DESCRIPTION.md", "hardproof.json"])
        (d / "Laws.lean").write_text(laws, encoding="utf-8")
        stage(bug, tag, d, task, ["Laws.lean"], f"{HP} check laws >/dev/null", "sonnet", log)
        if hp(d, "check", "laws").get("verdict") != "accept":
            return False
        laws = (d / "Laws.lean").read_text(encoding="utf-8")
        return True

    for step in range(1, max_steps + 1):
        # R: does the mirror pass the laws?
        r = domain(f"R{step}")
        stage(bug, f"R{step}", r, R_TASK, ["RefPassesSolution.lean", "ConflictSolution.lean"], f"{HP} check ref conflict >/dev/null", "sonnet", log)
        rep = hp(r, "check", "ref", "conflict", "--paranoid")
        kind = next((x.get("kind") for x in rep.get("results", []) if x.get("verdict") == "accept"), None)
        if kind is None:
            return done("prover failed")
        if kind == "conflict":
            q = hp(r, "question", "conflict").get("question") or {}
            line = (q.get("input") or {}).get("encoded") or ""
            a, c = oracle(r, pre, line), oracle(r, post, line)
            item = {"step": step, "kind": "conflict", "law": q.get("law"), "input": q.get("input"), "ref": q.get("ref"),
                    "pre": a, "post": c, "hits_the_fix": differ(line, a, c)}
            res["items"].append(item)
            if item["hits_the_fix"]:
                return done("detected by a conflict")
            if not law_round(f"LF{step}", LAW_FIX.format(law=q.get("law"), shown=(q.get("input") or {}).get("shown"),
                                                         ref=(q.get("ref") or {}).get("shown"), hp=HP)):
                return done("law author failed")
            continue
        # A: gap or complete.
        a_dir = domain(f"A{step}")
        stage(bug, f"A{step}", a_dir, A_TASK, ["GapSolution.lean", "CompleteSolution.lean"], f"{HP} check gap complete >/dev/null", "sonnet", log)
        rep = hp(a_dir, "check", "gap", "complete", "--paranoid")
        kind = next((x.get("kind") for x in rep.get("results", []) if x.get("verdict") == "accept"), None)
        if kind is None:
            return done("adversary failed")
        if kind == "complete":
            return done("complete, bug not detected")
        q = hp(a_dir, "question", "gap").get("question") or {}
        line = (q.get("input") or {}).get("encoded") or ""
        a, c = oracle(a_dir, pre, line), oracle(a_dir, post, line)
        item = {"step": step, "kind": "gap", "input": q.get("input"), "design_a": q.get("design_a"), "design_b": q.get("design_b"),
                "ref": q.get("ref"), "pre": a, "post": c, "hits_the_fix": differ(line, a, c)}
        res["items"].append(item)
        if not line:
            return done("no question text")
        if item["hits_the_fix"]:
            return done("detected by a question")
        if not law_round(f"LA{step}", LAW_ADD.format(shown=(q.get("input") or {}).get("shown"), a=(q.get("design_a") or {}).get("shown"),
                                                     b=(q.get("design_b") or {}).get("shown"), answer=c.get("out"), hp=HP)):
            return done("law author failed")
    return done("step limit")


def score() -> int:
    rows = [json.loads(p.read_text()) for p in sorted(OUT.glob("*.json"))]
    from collections import Counter
    c = Counter(r["outcome"] for r in rows)
    summary = {"bugs": len(rows), "outcomes": dict(c),
               "model_made": sum(1 for r in rows if r["outcome"] != "no model"),
               "bug_in_model_scope": sum(1 for r in rows if (r.get("model") or {}).get("bug_in_model_scope")),
               "detected": sum(1 for r in rows if str(r["outcome"]).startswith("detected")),
               "items_shown_to_the_human": sum(len(r["items"]) for r in rows),
               "items_not_the_bug": sum(1 for r in rows for i in r["items"] if not i["hits_the_fix"]),
               "cost_usd": round(sum(r.get("cost_usd") or 0 for r in rows), 2), "seconds": sum(r.get("seconds") or 0 for r in rows)}
    (HERE / "retro_score.json").write_text(json.dumps({"summary": summary, "rows": rows}, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["run", "score"])
    parser.add_argument("--only", nargs="*", default=[])
    parser.add_argument("--concurrency", type=int, default=8)
    parser.add_argument("--max-steps", type=int, default=6)
    args = parser.parse_args()
    if args.cmd == "score":
        return score()
    bugs = [b for b in json.loads((HERE / "bugs.json").read_text()) if b.get("verified") and (not args.only or b["id"] in args.only)]
    bugs = [b for b in bugs if not (OUT / f"{b['id']}.json").exists()]
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(lambda b: one(b, args.max_steps), bugs))
    print(json.dumps([{k: r.get(k) for k in ("bug", "title", "outcome", "cost_usd", "seconds")} for r in results], indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
