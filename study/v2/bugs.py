#!/usr/bin/env python3
"""Hard Proof v2: the data set of real bugs.

Stages (each is a command):
    trees     for each mined bug, write the package source before and after the fix
              into `~/Projects/hp-work/src/<bug id>/{pre,post}` (git archive, no history)
    repro     one worker for each bug writes `repro.py`: a function `run()` that calls the
              function under test on the failing input and returns a string
    verify    run each `repro.py` against the two trees; a bug is in the data set only
              when the two results differ. Writes `bugs.json`.

Usage:
    python3 bugs.py trees | repro [--concurrency N] [--only ID ...] | verify
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from flowrun import run_agent

HERE = Path(__file__).resolve().parent
WORK = Path.home() / "Projects" / "hp-work"
SRC = WORK / "src"
REPRO = WORK / "repro"
PKG = {"Puppetmaster": ["puppetmaster", "docs", "README.md"], "marionette": ["harness", "pmharness", "docs", "README.md"]}

RUNNER = r'''
import sys, json, traceback
sys.path.insert(0, sys.argv[1])
sys.dont_write_bytecode = True
ns = {}
try:
    exec(compile(open(sys.argv[2]).read(), sys.argv[2], "exec"), ns)
    out = ns["run"]()
    print(json.dumps({"ok": True, "result": out if isinstance(out, str) else repr(out)}))
except BaseException as e:
    print(json.dumps({"ok": False, "error": type(e).__name__, "message": str(e)[:300],
                      "where": traceback.format_exc().splitlines()[-3:]}))
'''


def bug_id(b: dict) -> str:
    return hashlib.sha256(f"{b['repo']}|{b['fix_commit']}|{b['function']}|{b['title']}".encode()).hexdigest()[:8]


def run_snippet(tree: Path, snippet: Path, timeout: int = 60) -> dict:
    """Run `run()` of a snippet file with `tree` first on the import path. A separate process, no bytecode."""
    try:
        p = subprocess.run([sys.executable, "-I", "-c", RUNNER, str(tree), str(snippet)], capture_output=True, text=True,
                           timeout=timeout, cwd=tree, env={"PATH": "/usr/bin:/bin", "HOME": str(WORK / "fakehome"),
                                                           "PYTHONDONTWRITEBYTECODE": "1"})
        line = [l for l in p.stdout.splitlines() if l.startswith("{")]
        return json.loads(line[-1]) if line else {"ok": False, "error": "no output", "message": p.stderr[-300:]}
    except subprocess.TimeoutExpired:
        return {"ok": False, "error": "timeout", "message": ""}


MISSING = ("ImportError", "AttributeError", "ModuleNotFoundError", "NameError")


def comparable(a: dict, b: dict) -> bool:
    """False when one side could not find the function (a fix can move or rename it). That says nothing about behavior."""
    return not any((not x.get("ok")) and x.get("error") in MISSING for x in (a, b))


def same(a: dict, b: dict) -> bool:
    if not comparable(a, b):
        return True
    if a.get("ok") and b.get("ok"):
        return a["result"] == b["result"]
    if not a.get("ok") and not b.get("ok"):
        return a.get("error") == b.get("error")
    return False


def load_raw() -> list[dict]:
    rows = json.loads((HERE / "bugs_raw.json").read_text())
    for b in rows:
        b["id"] = bug_id(b)
    return rows


def trees() -> int:
    n = 0
    for b in load_raw():
        repo = WORK / b["repo"]
        for side, commit in (("pre", b["parent_commit"]), ("post", b["fix_commit"])):
            dest = SRC / b["id"] / side
            if dest.exists():
                continue
            dest.mkdir(parents=True)
            paths = [p for p in PKG[b["repo"]] if subprocess.run(["git", "-C", str(repo), "cat-file", "-e", f"{commit}:{p}"]).returncode == 0]
            arch = subprocess.Popen(["git", "-C", str(repo), "archive", commit, *paths], stdout=subprocess.PIPE)
            subprocess.run(["tar", "-x", "-C", str(dest)], stdin=arch.stdout, check=False)
            arch.wait()
            n += 1
    print(json.dumps({"trees_written": n}))
    return 0


REPRO_BRIEF = """The folder `{pre}` has the Python source of a project at one commit. A bug report says that the function `{function}` in `{file}` gives a wrong result for one input.

The report:
- What is wrong: {what}
- The input: {inp}
- The result now: {wrong}
- The result that the reporter expects: {right}

Write one file, `repro.py`, in the current folder (`{folder}`). It must define `run()` with no arguments. `run()` imports the function from the project (the project folder will be the first entry of `sys.path`, so `import {top}` works), calls it on the input of the report, and returns a short string that shows the result (use `repr` or `json.dumps` with sorted keys). If the function needs small state (a clock, a temp folder, a fake object), build it inside `run()` with the standard library only. `run()` must be deterministic: no real time, no random values, no network, no paths outside a `tempfile.TemporaryDirectory()`. If the wrong result is an exception, catch it and return its class name.

Check your file: `cd {pre} && python3 -c "import sys; sys.path.insert(0, '.'); exec(open('{folder}/repro.py').read()); print(run())"` must print the result that the report calls "the result now". Read the function in `{pre}/{file}` first. Do not change the project folder. End with VERDICT: PASS when `repro.py` shows the reported result, or VERDICT: FAIL with the reason when you cannot make the project give the reported result."""


def repro_one(b: dict) -> dict:
    folder = REPRO / b["id"]
    pre = SRC / b["id"] / "pre"
    task = REPRO_BRIEF.format(pre=pre, folder=folder, function=b["function"], file=b["file"], what=b.get("what_was_wrong"),
                              inp=b.get("failing_input"), wrong=b.get("wrong_result"), right=b.get("right_result"),
                              top=PKG[b["repo"]][0])
    r = run_agent(folder, f"hp2-repro-{b['id']}", task, ["repro.py"], model="sonnet", shell=True,
                  check="test -s repro.py", timeout=1500)
    r["id"] = b["id"]
    return r


def verify() -> int:
    out = []
    for b in load_raw():
        snippet = REPRO / b["id"] / "repro.py"
        if not snippet.exists():
            b["verified"] = False
            b["verify_note"] = "no repro.py"
        else:
            a = run_snippet(SRC / b["id"] / "pre", snippet)
            c = run_snippet(SRC / b["id"] / "post", snippet)
            b["pre_result"], b["post_result"] = a, c
            b["verified"] = not same(a, c)
            b["verify_note"] = ("the two trees differ on the reported input" if b["verified"] else
                                "the function is absent on one side (moved or renamed by the fix)" if not comparable(a, c) else
                                "the two trees give the same result")
        out.append(b)
    (HERE / "bugs.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"mined": len(out), "verified": sum(1 for b in out if b["verified"]),
                      "not_verified": [(b["id"], b["title"][:50], b["verify_note"]) for b in out if not b["verified"]]}, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["trees", "repro", "verify"])
    parser.add_argument("--only", nargs="*", default=[])
    parser.add_argument("--concurrency", type=int, default=6)
    args = parser.parse_args()
    if args.cmd == "trees":
        return trees()
    if args.cmd == "verify":
        return verify()
    todo = [b for b in load_raw() if (not args.only or b["id"] in args.only) and not (REPRO / b["id"] / "repro.py").exists()]
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(repro_one, todo))
    path = HERE / "repro_runs.json"
    old = json.loads(path.read_text()) if path.exists() else []
    path.write_text(json.dumps(old + results, indent=1) + "\n", encoding="utf-8")
    print(json.dumps([{k: r.get(k) for k in ("id", "flow_status", "seconds", "cost_usd", "error")} for r in results], indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
