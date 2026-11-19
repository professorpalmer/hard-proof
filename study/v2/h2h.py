#!/usr/bin/env python3
"""Hard Proof v2: one blind verify step for the findings of three review tools on one release range.

The rules are in `h2h/PROTOCOL.md`. This script does not run the tools. It reads their findings,
makes one list without the name of the tool, and gives that list to two verifier agents.

Usage:
    python3 h2h.py collect     # hpf findings + h2h/findings_<arm>.json -> h2h/claims_all.json, h2h/claims.json
    python3 h2h.py verify      # two verifier agents, results in h2h/verify_<model>.json
    python3 h2h.py summary     # h2h/result.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from bugs import WORK
from flowrun import run_agent

HERE = Path(__file__).resolve().parent
OUT = HERE / "h2h"
RUNS = WORK / "h2h" / "verify"
SNAP = WORK / "audit-pm-1510-lean" / "src"
HPF = WORK / "audit-pm-1510-lean" / "review.json"
ARMS = ("hpf", "claude", "codex")
PY = str(Path.home() / "Projects" / "Puppetmaster" / ".venv" / "bin" / "python")

VERIFY = """The folder `project/` has the current source of the product `Puppetmaster` at one release (Python package, tests and documentation). Reviews of the newest change made {n} claims about that release. `claims.json` lists the claims.

Your work: decide for each claim what it is. Read the function, its docstring and comments, the documentation, the tests in `project/tests` that cover it, and each caller in the product (use grep). You can write and run a check (use `{py}` as the Python, with `project/` as the current folder for imports). Then give one verdict for each claim:

- `real`: the result is wrong, and the product can hit it. You must name a caller (file and line) that can pass such an input in normal use, and say in one sentence what goes wrong for the user or for the product.
- `real_unreachable`: the result conflicts with the docstring, the documentation or the clear contract of the function, but no caller in the product can pass such an input today.
- `intended`: the behavior is by design. You must quote the comment, the documentation, the test, or the caller that depends on it.
- `unclear`: the evidence does not decide it. Say what decision the owner must make.

Be strict. A claim is `real` only when you can show the path from normal use of the product to the wrong result.

Write one file, `verdicts.json`, in the current folder: a JSON list with one entry for each claim:
{{"k": 1, "verdict": "real | real_unreachable | intended | unclear", "duplicate_of": null or the k of an earlier claim that states the same fault, "what_goes_wrong": "one sentence, or null", "caller": "path:line, or null", "evidence": "the quote or the path:line that supports the verdict", "severity": "high | medium | low | none"}}

Do not change `project/`. End with `VERDICT: PASS` when `verdicts.json` has one entry for each claim."""

VERIFY_CHECK = ("python3 -c \"import json;d=json.load(open('verdicts.json'));c=json.load(open('claims.json'));"
                "assert {x['k'] for x in d}=={x['k'] for x in c};"
                "assert all(x['verdict'] in ('real','real_unreachable','intended','unclear') for x in d);"
                "assert all(x.get('caller') for x in d if x['verdict']=='real')\" && echo OK")


def load(name: str):
    path = OUT / name
    return json.loads(path.read_text()) if path.exists() else None


def save(name: str, data) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")


def collect() -> int:
    rows = []
    for f in json.loads(HPF.read_text())["findings"]:
        rows.append({"arm": "hpf", "claim": f["claim"], "file": f["file"], "function": f["function"]})
    for arm in ARMS[1:]:
        found = load(f"findings_{arm}.json")
        if found is None:
            print(f"absent: h2h/findings_{arm}.json")
            return 1
        for f in found:
            rows.append({"arm": arm, "claim": f["claim"], "file": f.get("file"), "function": f.get("function")})
    random.Random(1).shuffle(rows)
    for k, row in enumerate(rows, 1):
        row["k"] = k
    save("claims_all.json", rows)
    save("claims.json", [{k: row[k] for k in ("k", "claim", "file", "function")} for row in rows])
    print(json.dumps({arm: sum(1 for r in rows if r["arm"] == arm) for arm in ARMS}))
    return 0


def verify() -> int:
    claims = load("claims.json")
    chunks = [claims[i:i + 9] for i in range(0, len(claims), 9)]

    def one(job) -> dict:
        model, n = job
        name = f"verify_{model}_{n}.json"
        stored = load(name)
        if stored:
            return stored
        folder = RUNS / hashlib.sha256(f"h2h|{model}|{n}".encode()).hexdigest()[:10]
        if folder.exists():
            shutil.rmtree(folder)
        folder.mkdir(parents=True)
        subprocess.run(["cp", "-Rc", str(SNAP), str(folder / "project")], check=True)
        (folder / ".gitignore").write_text("__pycache__/\n*.pyc\n.pytest_cache/\n", encoding="utf-8")
        (folder / "claims.json").write_text(json.dumps(chunks[n], indent=1) + "\n", encoding="utf-8")
        r = run_agent(folder, f"h2h-{folder.name}", VERIFY.format(n=len(chunks[n]), py=PY), ["verdicts.json"], model=model,
                      shell=True, check=VERIFY_CHECK, timeout=3600, extra_allowed=[f"Bash({PY}:*)"])
        try:
            r.update(model=model, chunk=n, verdicts=json.loads((folder / "verdicts.json").read_text()))
        except Exception:
            r.update(model=model, chunk=n, verdicts=None)
        save(name, r)
        return r

    jobs = [(model, n) for n in range(len(chunks)) for model in ("opus", "sonnet")]
    with ThreadPoolExecutor(max_workers=3) as pool:
        runs = list(pool.map(one, jobs))
    for model in ("opus", "sonnet"):
        mine = [r for r in runs if r.get("model") == model]
        save(f"verify_{model}.json", {"model": model, "cost_usd": round(sum(r.get("cost_usd") or 0 for r in mine), 4),
                                      "seconds": sum(r.get("seconds") or 0 for r in mine),
                                      "verdicts": [v for r in mine for v in (r.get("verdicts") or [])]})
    print(json.dumps({"claims": len(claims), "runs": len(runs), "cost_usd": round(sum(r.get("cost_usd") or 0 for r in runs), 2),
                      "verdict_lists": [len(r.get("verdicts") or []) for r in runs]}))
    return 0


def summary() -> int:
    rows = load("claims_all.json")
    verdicts = {m: {v["k"]: v for v in ((load(f"verify_{m}.json") or {}).get("verdicts") or [])} for m in ("opus", "sonnet")}
    merge = load("merge.json") or {}
    for row in rows:
        row["verdicts"] = {m: (verdicts[m].get(row["k"]) or {}).get("verdict") for m in verdicts}
        row["confirmed"] = all(v == "real" for v in row["verdicts"].values())
        row["bug"] = merge.get(str(row["k"]), f"k{row['k']}")
    arms = {}
    for arm in ARMS:
        mine = [r for r in rows if r["arm"] == arm]
        bugs = {r["bug"] for r in mine if r["confirmed"]}
        others = {r["bug"] for r in rows if r["arm"] != arm and r["confirmed"]}
        arms[arm] = {"findings": len(mine), "confirmed_claims": sum(1 for r in mine if r["confirmed"]),
                     "confirmed_distinct_bugs": len(bugs), "only_this_arm": len(bugs - others), "bugs": sorted(bugs)}
    out = {"range": "v1.50.0..v1.51.1", "arms": arms,
           "union_distinct_bugs": len({r["bug"] for r in rows if r["confirmed"]}),
           "verifier_cost_usd": round(sum((load(f"verify_{m}.json") or {}).get("cost_usd") or 0 for m in ("opus", "sonnet")), 2),
           "claims": [{k: r[k] for k in ("k", "arm", "file", "function", "verdicts", "confirmed", "bug")} for r in rows]}
    save("result.json", out)
    print(json.dumps({"arms": arms, "union": out["union_distinct_bugs"], "verifier_cost_usd": out["verifier_cost_usd"]}, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("step", choices=["collect", "verify", "summary"])
    args = parser.parse_args()
    return {"collect": collect, "verify": verify, "summary": summary}[args.step]()


if __name__ == "__main__":
    sys.exit(main())
