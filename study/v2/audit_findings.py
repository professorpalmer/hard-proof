#!/usr/bin/env python3
"""Hard Proof v2: audit the review findings that are not a known historical bug.

A finding is a candidate when its repro gives the same result on the newest dev source as on the
source that the reviewer read. Two verifier agents (different models, separate folders) then judge
each candidate on the newest source: real and reachable, real but not reachable, intended, or unclear.

Usage:
    python3 audit_findings.py collect
    python3 audit_findings.py run [--models opus sonnet] [--concurrency 12] [--only GROUP ...]
    python3 audit_findings.py merge
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from bugs import PKG, SRC, WORK, run_snippet
from flowrun import run_agent

HERE = Path(__file__).resolve().parent
RUNS = WORK / "v"
DEV = SRC / "_dev"
SUBSET = {"Puppetmaster": ["puppetmaster", "tests", "docs", "README.md", "pyproject.toml"],
          "marionette": ["harness", "pmharness", "tests", "docs", "README.md", "pyproject.toml"]}

BRIEF = """The folder `project/` has the current source of the product `{repo}` (Python package, tests and documentation). A code review made {n} claims about one function: `{function}` in `project/{file}`. Some claims can be wrong, and some can be the same claim two times.

`claims.json` lists the claims. For claim `k`, the file `claim_<k>.py` defines `run()`, which calls the function on the input of the claim, and `claims.json` has the result that `run()` gives on the current source (`result_now`). You can run a claim again: `cd project && python3 -c "import sys; sys.path.insert(0, '.'); exec(open('../claim_1.py').read()); print(run())"`.

Your work: decide for each claim what it is. Read the function, its docstring and comments, the documentation, the tests in `project/tests` that cover it, and each caller of the function in the product (use grep). Then give one verdict:

- `real`: the result is wrong, and the product can hit it. You must name a caller (file and line) that can pass such an input in normal use, and say in one sentence what goes wrong for the user or for the product.
- `real_unreachable`: the result conflicts with the docstring, the documentation or the clear contract of the function, but no caller in the product can pass such an input today.
- `intended`: the behavior is by design. You must quote the comment, the documentation, the test, or the caller that depends on it.
- `unclear`: the evidence does not decide it. Say what decision the owner must make.

Be strict. A claim is `real` only when you can show the path from normal use of the product to the wrong result. A test in `project/tests` that asserts the current behavior is strong evidence for `intended`, unless the test itself conflicts with the documentation.

Write one file, `verdicts.json`, in the current folder: a JSON list with one entry for each claim:
{{"k": 1, "verdict": "real | real_unreachable | intended | unclear", "duplicate_of": null or the k of an earlier claim that states the same fault, "what_goes_wrong": "one sentence, or null", "caller": "path:line of the caller that reaches it, or null", "evidence": [{{"file": "path", "line": 12, "quote": "exact text"}}], "severity": "high | medium | low", "fix_idea": "one or two sentences, or null"}}

Do not change `project/`. Do not write other files, except scratch files in `.lake/`. End with `VERDICT: PASS` when `verdicts.json` has one entry for each claim."""

CHECK = "python3 -c \"import json;d=json.load(open('verdicts.json'));c=json.load(open('claims.json'));assert {x['k'] for x in d}=={x['k'] for x in c};assert all(x['verdict'] in ('real','real_unreachable','intended','unclear') for x in d)\""


def collect() -> int:
    score = json.loads((HERE / "review_score.json").read_text())
    bugs = {b["id"]: b for b in json.loads((HERE / "bugs.json").read_text())}
    out = []
    for r in score["rows"]:
        b = bugs[r["bug"]]
        for i in r["items"]:
            if "pre" not in i or (r["side"] == "pre" and i.get("hits_the_fix")):
                continue
            seen = i["pre"] if r["side"] == "pre" else i["post"]
            head = i.get("head") or {}
            if not (seen.get("ok") and head.get("ok") and seen["result"] == head["result"]):
                continue
            out.append({"run": r["run"], "arm": f"{r['arm']}/{r['model']}/{r['side']}", "bug": r["bug"], "n": i["n"],
                        "repo": b["repo"], "file": b["file"], "function": b["function"], "claim": i.get("claim"),
                        "expected": i.get("expected"), "result_now": head["result"]})
    groups: dict = {}
    for c in out:
        key = hashlib.sha256(f"{c['repo']}|{c['file']}|{c['function']}".encode()).hexdigest()[:8]
        g = groups.setdefault(key, {"group": key, "repo": c["repo"], "file": c["file"], "function": c["function"], "claims": []})
        c["k"] = len(g["claims"]) + 1
        g["claims"].append(c)
    (HERE / "audit_groups.json").write_text(json.dumps(list(groups.values()), indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"candidates": len(out), "functions": len(groups),
                      "by_repo": {r: sum(1 for c in out if c["repo"] == r) for r in SUBSET}}))
    return 0


def one(g: dict, model: str) -> dict:
    rid = hashlib.sha256(f"hp2v|{g['group']}|{model}".encode()).hexdigest()[:10]
    folder = RUNS / rid
    if folder.exists():
        shutil.rmtree(folder)
    (folder / "project").mkdir(parents=True)
    for name in SUBSET[g["repo"]]:
        src = DEV / g["repo"] / name
        if src.is_dir():
            subprocess.run(["cp", "-Rc", str(src), str(folder / "project" / name)], check=False)
        elif src.exists():
            shutil.copy(src, folder / "project" / name)
    (folder / ".gitignore").write_text(".lake/\n__pycache__/\n*.pyc\n", encoding="utf-8")
    claims = []
    for c in g["claims"]:
        shutil.copy(WORK / "r" / c["run"] / f"finding_{c['n']}.py", folder / f"claim_{c['k']}.py")
        claims.append({"k": c["k"], "claim": c["claim"], "expected_by_the_review": c["expected"], "result_now": c["result_now"]})
    (folder / "claims.json").write_text(json.dumps(claims, indent=1) + "\n", encoding="utf-8")
    task = BRIEF.format(repo=g["repo"], n=len(claims), function=g["function"], file=g["file"])
    r = run_agent(folder, f"hp2-{rid}", task, ["verdicts.json"], model=model, shell=True, check=CHECK, timeout=3000)
    r.update(group=g["group"], model=model, run=rid)
    try:
        r["verdicts"] = json.loads((folder / "verdicts.json").read_text())
    except Exception:
        r["verdicts"] = None
    return r


def merge() -> int:
    groups = {g["group"]: g for g in json.loads((HERE / "audit_groups.json").read_text())}
    runs = json.loads((HERE / "audit_runs.json").read_text())
    rows = []
    for g in groups.values():
        mine = {r["model"]: {v["k"]: v for v in (r.get("verdicts") or [])} for r in runs if r["group"] == g["group"]}
        for c in g["claims"]:
            vs = {m: d.get(c["k"]) for m, d in mine.items()}
            verdicts = {m: (v or {}).get("verdict") for m, v in vs.items()}
            rows.append({"group": g["group"], "k": c["k"], "repo": g["repo"], "file": g["file"], "function": g["function"],
                         "claim": c["claim"], "result_now": c["result_now"], "run": c["run"], "n": c["n"], "verdicts": verdicts,
                         "agree_real": len(verdicts) >= 2 and all(v == "real" for v in verdicts.values()),
                         "any_real": any(v == "real" for v in verdicts.values()),
                         "details": vs})
    (HERE / "audit_merged.json").write_text(json.dumps(rows, indent=1) + "\n", encoding="utf-8")
    from collections import Counter
    print(json.dumps({"claims": len(rows), "both_real": sum(1 for r in rows if r["agree_real"]),
                      "one_real": sum(1 for r in rows if r["any_real"] and not r["agree_real"]),
                      "pairs": Counter(" / ".join(f"{m}:{v}" for m, v in sorted(r["verdicts"].items())) for r in rows).most_common(12),
                      "cost_usd": round(sum(r.get("cost_usd") or 0 for r in runs), 2)}, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["collect", "run", "merge"])
    parser.add_argument("--models", nargs="+", default=["opus", "sonnet"])
    parser.add_argument("--only", nargs="*", default=[])
    parser.add_argument("--concurrency", type=int, default=12)
    args = parser.parse_args()
    if args.cmd == "collect":
        return collect()
    if args.cmd == "merge":
        return merge()
    groups = [g for g in json.loads((HERE / "audit_groups.json").read_text()) if not args.only or g["group"] in args.only]
    jobs = [(g, m) for g in groups for m in args.models]
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(lambda gm: one(*gm), jobs))
    path = HERE / "audit_runs.json"
    old = json.loads(path.read_text()) if path.exists() else []
    done = {r["run"] for r in results}
    path.write_text(json.dumps([r for r in old if r["run"] not in done] + results, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"ran": len(results), "no_verdicts": [r["run"] for r in results if not r.get("verdicts")],
                      "cost_usd": round(sum(r.get("cost_usd") or 0 for r in results), 2)}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
