#!/usr/bin/env python3
"""Hard Proof v2: audit the conflict certificates of the proof pipeline that are not the known bug.

A conflict certificate is a machine-checked proof that the mirror of a function breaks one law on one
legal input. The law is an agent's reading of one quoted sentence of the documentation. So a conflict
says "the code and this reading of the documentation do not agree". It does not say which is wrong.

Steps:
    collect   run each conflict input on the newest released source. A conflict is a candidate when
              the function gives the same result there as on the source of the pipeline run.
    run       two verifier agents (different models, separate folders) judge each candidate:
              the code is wrong, the documentation is wrong, or the law author read too much.
    merge     one row for each candidate with the two verdicts.

Usage:
    python3 conflict_audit.py collect
    python3 conflict_audit.py run [--models opus sonnet] [--concurrency 5] [--only GROUP ...]
    python3 conflict_audit.py merge
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from bugs import SRC, WORK
from flowrun import run_agent
from retro import TOOL, oracle, sid

HERE = Path(__file__).resolve().parent
RUNS = WORK / "c"
OUT = HERE / "conflict_audit"
HEAD = SRC / "_head"
TAGS = {"Puppetmaster": "v1.51.2", "marionette": "v0.9.685"}
SUBSET = {"Puppetmaster": ["puppetmaster", "tests", "docs", "README.md", "pyproject.toml"],
          "marionette": ["harness", "pmharness", "tests", "docs", "README.md", "pyproject.toml"]}
VERDICTS = ("real", "real_unreachable", "doc_wrong", "misread", "unclear")

CLAIM_PY = '''"""Claim {k}: call the function on the input of the claim. `run()` returns the repr of the result."""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LINE = {line!r}


def case():
    sys.path.insert(0, str(HERE / "_hp"))
    from hpflow.proof.checks import load_adapter
    from hpflow.proof.domain import Domain
    from hpflow.proof.link import load_function
    domain = Domain(HERE / "domain_{k}")
    adapter = load_adapter(domain)
    _, function = load_function(domain.config(), HERE / "project")
    return adapter, function, adapter.decode(LINE)


def run():
    adapter, function, args = case()
    return repr(adapter.call(function, args))


if __name__ == "__main__":
    print(run())
'''

BRIEF = """The folder `project/` has the current source of the product `{repo}` (Python package, tests and documentation). A proof tool made {n} claims about one function: `{function}` in `project/{file}`.

Each claim has this form. An agent read one sentence of the docstring or the documentation and wrote it as a formal law. A checker then proved that the function breaks that law for one input. The function really gives that result: `claim_<k>.py` defines `run()`, which calls the function on the input, and `claims.json` has the result on the current source (`result_now`). `domain_<k>/link_adapter.py` shows how the input is built (`decode` and `call`). So the code and the law do not agree. Your work is to decide which is wrong.

`claims.json` has, for each claim `k`: the law (Lean text, with the quoted sentence in its comment), the input in readable form, and the result.

Read the function, its docstring and comments, the documentation, the tests in `project/tests` that cover it, and each caller of the function in the product (use grep). Then give one verdict for each claim:

- `real`: the quoted sentence states the intended behavior, the code breaks it, and the product can hit it. You must name a caller (file and line) that can pass such an input in normal use, and say in one sentence what goes wrong for the user or for the product.
- `real_unreachable`: the quoted sentence states the intended behavior and the code breaks it, but no caller in the product can pass such an input today.
- `doc_wrong`: the behavior of the code is by design (a comment, a test or a caller depends on it), and the quoted sentence, as it is written, is false or misleads a reader for this input. The fix is a change of the sentence. You must quote the evidence for the design and say which words of the sentence are wrong.
- `misread`: the law says more than the quoted sentence says, or the input is outside what the sentence is about. A careful reader of the sentence does not expect a different result. No fix is necessary.
- `unclear`: the evidence does not decide it. Say what decision the owner must make.

Be strict. A claim is `real` only when you can show the path from normal use of the product to the wrong result. A test in `project/tests` that asserts the current behavior is strong evidence against `real`. Do not select `doc_wrong` only because the sentence is short: select it when a reader who trusts the sentence gets a wrong expectation for an input that can occur.

Write one file, `verdicts.json`, in the current folder: a JSON list with one entry for each claim:
{{"k": 1, "verdict": "real | real_unreachable | doc_wrong | misread | unclear", "duplicate_of": null or the k of an earlier claim that states the same fault, "what_goes_wrong": "one sentence, or null", "caller": "path:line of the caller that reaches it, or null", "evidence": "the quote or the path:line that supports the verdict", "fix": "one sentence: the smallest change of the code or of the sentence, or null", "severity": "high | medium | low | none"}}

Do not change `project/`. Do not write other files, except scratch files in `.lake/`. End with `VERDICT: PASS` when `verdicts.json` has one entry for each claim."""

CHECK = ("python3 -c \"import json;d=json.load(open('verdicts.json'));c=json.load(open('claims.json'));"
         "assert {x['k'] for x in d}=={x['k'] for x in c};"
         "assert all(x['verdict'] in ('real','real_unreachable','doc_wrong','misread','unclear') for x in d);"
         "assert all(x.get('caller') for x in d if x['verdict']=='real')\" && echo OK")


def head_trees() -> None:
    for repo, tag in TAGS.items():
        dest = HEAD / repo
        if (dest / ".tag").exists() and (dest / ".tag").read_text().strip() == tag:
            continue
        if dest.exists():
            shutil.rmtree(dest)
        dest.mkdir(parents=True)
        clone = WORK / repo
        subprocess.run(["git", "-C", str(clone), "fetch", "-q", "gh", "--tags"], check=False)
        archive = subprocess.run(["git", "-C", str(clone), "archive", tag, *SUBSET[repo]], capture_output=True, check=True)
        subprocess.run(["tar", "-x", "-C", str(dest)], input=archive.stdout, check=True)
        (dest / ".tag").write_text(tag + "\n", encoding="utf-8")


def law_text(laws: str, name: str) -> str:
    """The definition of one law with its doc comment."""
    found = re.search(r"(/--(?:(?!/--).)*?-/\s*)?def\s+" + re.escape(name) + r"\b.*?(?=\n\s*\n(?:/--|def |theorem |end |namespace |@\[)|\Z)", laws, flags=re.S)
    return found.group(0).strip() if found else ""


def collect() -> int:
    head_trees()
    bugs = {b["id"]: b for b in json.loads((HERE / "bugs.json").read_text())}
    out, dropped = [], Counter()
    for path in sorted((HERE / "retro").glob("*.json")):
        r = json.loads(path.read_text())
        b = bugs[r["bug"]]
        for i in r["items"]:
            if i["kind"] != "conflict" or i["hits_the_fix"]:
                continue
            folder = WORK / "p" / sid(r["bug"], f"R{i['step']}")
            solution = folder / "ConflictSolution.lean"
            if not (solution.exists() and f"hardproof-law: {i['law']}" in solution.read_text(errors="replace")):
                dropped["stage folder absent or changed"] += 1
                continue
            line = (i.get("input") or {}).get("encoded") or ""
            now = oracle(folder, HEAD / b["repo"], line)
            pre = i["pre"]
            if not now.get("ok") and now.get("out") in ("DomainError", "ImportError", "AttributeError", "ModuleNotFoundError", "no output", "timeout"):
                dropped["function absent on the newest source"] += 1
                continue
            if (now.get("ok"), now.get("out")) != (pre.get("ok"), pre.get("out")):
                dropped["result changed on the newest source"] += 1
                continue
            text = law_text((folder / "Laws.lean").read_text(errors="replace"), i["law"])
            if not text:
                dropped["law text not found"] += 1
                continue
            out.append({"bug": r["bug"], "step": i["step"], "repo": b["repo"], "file": b["file"], "function": b["function"],
                        "law": i["law"], "law_text": text, "input": (i.get("input") or {}).get("shown"), "line": line,
                        "result_shown": (i.get("ref") or {}).get("shown"), "result_encoded": now.get("out"), "folder": str(folder)})
    groups: dict = {}
    for c in out:
        key = hashlib.sha256(f"{c['repo']}|{c['file']}|{c['function']}".encode()).hexdigest()[:8]
        g = groups.setdefault(key, {"group": key, "repo": c["repo"], "file": c["file"], "function": c["function"], "claims": []})
        if any(x["law_text"] == c["law_text"] and x["line"] == c["line"] for x in g["claims"]):
            dropped["same law and input as an earlier claim"] += 1
            continue
        c["k"] = len(g["claims"]) + 1
        g["claims"].append(c)
    kept = sum(len(g["claims"]) for g in groups.values())
    (HERE / "conflict_groups.json").write_text(json.dumps(list(groups.values()), indent=1) + "\n", encoding="utf-8")
    summary = {"conflicts_not_the_known_bug": kept + sum(dropped.values()), "candidates": kept, "functions": len(groups), "dropped": dict(dropped),
               "by_repo": {r: sum(len(g["claims"]) for g in groups.values() if g["repo"] == r) for r in SUBSET}, "tags": TAGS}
    (HERE / "conflict_collect.json").write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))
    return 0


def build(g: dict, folder: Path) -> list[dict]:
    if folder.exists():
        shutil.rmtree(folder)
    (folder / "project").mkdir(parents=True)
    for name in SUBSET[g["repo"]]:
        src = HEAD / g["repo"] / name
        if src.is_dir():
            subprocess.run(["cp", "-Rc", str(src), str(folder / "project" / name)], check=False)
        elif src.exists():
            shutil.copy(src, folder / "project" / name)
    (folder / "_hp").mkdir()
    shutil.copytree(TOOL / "hpflow", folder / "_hp" / "hpflow", ignore=shutil.ignore_patterns("__pycache__"))
    (folder / ".gitignore").write_text(".lake/\n__pycache__/\n*.pyc\n", encoding="utf-8")
    claims = []
    for c in g["claims"]:
        domain = folder / f"domain_{c['k']}"
        domain.mkdir()
        for name in ("hardproof.json", "link_adapter.py"):
            shutil.copy(Path(c["folder"]) / name, domain / name)
        (folder / f"claim_{c['k']}.py").write_text(CLAIM_PY.format(k=c["k"], line=c["line"]), encoding="utf-8")
        done = subprocess.run([sys.executable, f"claim_{c['k']}.py"], cwd=folder, capture_output=True, text=True, timeout=120)
        claims.append({"k": c["k"], "law": c["law"], "law_text": c["law_text"], "input": c["input"],
                       "result_now": done.stdout.strip()[-2000:] if done.returncode == 0 else f"error: {done.stderr.strip()[-300:]}",
                       "result_in_the_form_of_the_proof_tool": c["result_shown"]})
    (folder / "claims.json").write_text(json.dumps(claims, indent=1) + "\n", encoding="utf-8")
    return claims


def one(g: dict, model: str) -> dict:
    rid = hashlib.sha256(f"hp2c|{g['group']}|{model}".encode()).hexdigest()[:10]
    stored = OUT / f"{rid}.json"
    if stored.exists():
        return json.loads(stored.read_text())
    folder = RUNS / rid
    claims = build(g, folder)
    task = BRIEF.format(repo=g["repo"], n=len(claims), function=g["function"], file=g["file"])
    r = run_agent(folder, f"hp2-{rid}", task, ["verdicts.json"], model=model, shell=True, check=CHECK, timeout=3000)
    r.update(group=g["group"], model=model, run=rid, claims=len(claims))
    try:
        r["verdicts"] = json.loads((folder / "verdicts.json").read_text())
    except Exception:
        r["verdicts"] = None
    OUT.mkdir(exist_ok=True)
    stored.write_text(json.dumps(r, indent=1) + "\n", encoding="utf-8")
    return r


def merge() -> int:
    groups = {g["group"]: g for g in json.loads((HERE / "conflict_groups.json").read_text())}
    runs = [json.loads(p.read_text()) for p in sorted(OUT.glob("*.json"))]
    rows = []
    for g in groups.values():
        mine = {r["model"]: {v["k"]: v for v in (r.get("verdicts") or [])} for r in runs if r["group"] == g["group"]}
        for c in g["claims"]:
            vs = {m: d.get(c["k"]) for m, d in mine.items()}
            verdicts = {m: (v or {}).get("verdict") for m, v in vs.items()}
            same = len(verdicts) >= 2 and len(set(verdicts.values())) == 1
            rows.append({"group": g["group"], "k": c["k"], "bug": c["bug"], "step": c["step"], "repo": g["repo"], "file": g["file"],
                         "function": g["function"], "law": c["law"], "law_text": c["law_text"], "input": c["input"],
                         "result": c["result_shown"], "verdicts": verdicts, "agreed": next(iter(verdicts.values())) if same else None,
                         "details": vs})
    (HERE / "conflict_merged.json").write_text(json.dumps(rows, indent=1) + "\n", encoding="utf-8")
    agreed = Counter(r["agreed"] or "the two do not agree" for r in rows)
    summary = {"claims": len(rows), "runs": len(runs), "agreed": dict(agreed),
               "pairs": Counter(" / ".join(f"{m}:{v}" for m, v in sorted(r["verdicts"].items())) for r in rows).most_common(15),
               "cost_usd": round(sum(r.get("cost_usd") or 0 for r in runs), 2), "seconds": sum(r.get("seconds") or 0 for r in runs)}
    (HERE / "conflict_summary.json").write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["collect", "run", "merge"])
    parser.add_argument("--models", nargs="+", default=["opus", "sonnet"])
    parser.add_argument("--only", nargs="*", default=[])
    parser.add_argument("--concurrency", type=int, default=5)
    args = parser.parse_args()
    if args.cmd == "collect":
        return collect()
    if args.cmd == "merge":
        return merge()
    groups = [g for g in json.loads((HERE / "conflict_groups.json").read_text()) if not args.only or g["group"] in args.only]
    jobs = [(g, m) for g in groups for m in args.models]
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(lambda gm: one(*gm), jobs))
    print(json.dumps({"ran": len(results), "no_verdicts": [r["run"] for r in results if not r.get("verdicts")],
                      "cost_usd": round(sum(r.get("cost_usd") or 0 for r in results), 2)}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
