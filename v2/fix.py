#!/usr/bin/env python3
"""Hard Proof v2: write a fix and a regression test for each confirmed bug, one worker for each source file.

Each worker has its own git worktree, cut from the newest `dev` of the repository (in the pilot's clone,
not in the owner's checkout). A check runs the repros and the tests. A judge reviews the diff.

Usage:
    python3 fix.py plan
    python3 fix.py run [--only SLUG ...] [--concurrency 8]
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import guard
from bugs import WORK
from flowrun import job_record, parse_json, sh

HERE = Path(__file__).resolve().parent
FIX = WORK / "fix"
INFO = WORK / "fixinfo"
RULES = {
    "Puppetmaster": "Python 3.9 is the floor: no `match`, no `X | Y` unions in annotations that run. Standard library only. `from __future__ import annotations` at the top of a new module. Tests are `unittest.TestCase` classes that also run with pytest, with no network and no real subprocess.",
    "marionette": "The harness is standard library only. `from __future__ import annotations` at the top of a new module. UTF-8 for each text file read or write. Tests are pytest tests with no network. `pmharness/intent.py` must stay pure and must not import Puppetmaster.",
}

BUILD = """This folder is a git worktree of the product `{repo}`, at the newest `dev` commit. A code review found {n} bugs in `{file}`. Two independent reviewers confirmed each one on this source: the result is wrong, and a caller in the product can reach it.

The bugs:

{bugs}

For bug `<id>` and claim `<k>`, the file `{info}/<id>_claim_<k>.py` defines `run()`, which shows the wrong result on this source (the listed "result now"). Read these files with `cat`.

Your work:
1. Read the function, its callers and its tests. Make sure that you understand each bug. If you find that one is not a bug (the behavior is by design), do not change the code for it: say so in your report with the evidence.
2. Fix each bug with the smallest change that corrects it. Do not change behavior that the bugs do not need. Do not refactor. Keep each existing test green: if an existing test asserts the wrong behavior, name it in your report and correct that one assertion.
3. Write regression tests in the new file `{test_file}`: for each bug at least one test that fails on the old code and passes on the fixed code, and one test for a near input that must keep its old result.
4. Run the tests only through the test runner of this task: `{runner} {test_file}` (it runs pytest with the right Python, one test run at a time on this machine, so it can wait). Give it the new test file and at most four existing test files that cover this module. Never run the whole test suite, never start a test run in the background, and never call pytest in another way: other workers share this machine and its memory.

Rules of this repository: {rules} No emojis. Comments and docstrings in short plain sentences; a comment says why, not what. Edit `{file}` and `{test_file}`. Edit a second source file only when the same fault is in a sibling code path that must change together with it (for example a second caller that builds the same value in the same wrong way), and name each such file in your report. Edit an existing test file only when it asserts the wrong behavior. Do not commit.

The check after your work: `python3 {check} {info}` (each repro must give a new result, the new tests and the related tests must pass). Run it yourself.

Report: for each bug, the cause in one sentence and the change in one sentence. End with `VERDICT: PASS` when each bug is fixed or shown to be by design, else `VERDICT: PARTIAL - <what is open>`."""

JUDGE = """Review the uncommitted change in this git worktree of `{repo}` (`git diff` and the new file `{test_file}`). The change must fix these confirmed bugs in `{file}`:

{bugs}

Rubric. Give FAIL when one item fails, and list each problem as `path:line - what`:
1. Each bug is fixed at its cause, or the report shows with evidence that it is by design. A fix that only hides the repro input is a failure.
2. The change is minimal: no refactor, no unrelated edit, no new dependency.
3. No behavior changes for inputs that the bugs do not cover. Check the callers of the function.
4. Each new test asserts the correct behavior and fails on the old code (read the test and the old code, or run it against `git stash`-free means: `git show HEAD:{file}`).
5. The code follows the rules of the repository: {rules} No emojis.
6. No existing test was weakened, except an assertion that tested the wrong behavior of one of these bugs.

You can run `{runner} {test_file}` (one test run at a time on this machine; never the whole suite). Do not edit files."""


def slug_of(repo: str, file: str) -> str:
    return ("pm-" if repo == "Puppetmaster" else "mn-") + re.sub(r"[^a-z0-9]+", "-", file.lower().replace(".py", "")).strip("-")


def plan() -> list[dict]:
    bugs = json.loads((HERE / "confirmed_bugs.json").read_text())
    groups: dict = {}
    for b in bugs:
        s = slug_of(b["repo"], b["file"])
        g = groups.setdefault(s, {"slug": s, "repo": b["repo"], "file": b["file"],
                                  "test_file": f"tests/test_hpfix_{s[3:].replace('-', '_')}.py", "bugs": []})
        g["bugs"].append(b)
    out = list(groups.values())
    (HERE / "fix_plan.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    return out


def bug_text(g: dict) -> str:
    rows = []
    for b in g["bugs"]:
        rows.append(f"- Bug `{b['id']}` in `{b['function']}` (claims {', '.join(str(k) for k in b['claims'])}).\n"
                    f"  What goes wrong: {b['what_goes_wrong']}\n  The review said: {b['claim']}\n"
                    f"  Result now: {b['result_now']}\n  A caller that reaches it: {b['caller']}\n  Fix idea of a reviewer (not binding): {b['fix_idea']}")
    return "\n".join(rows)


def one(g: dict) -> dict:
    repo = WORK / g["repo"]
    tree = FIX / g["slug"]
    info = INFO / g["slug"]
    if tree.exists():
        sh(["git", "-C", str(repo), "worktree", "remove", "--force", str(tree)], repo)
        shutil.rmtree(tree, ignore_errors=True)
    sh(["git", "-C", str(repo), "branch", "-D", f"hpfix/{g['slug']}"], repo)
    code, out = sh(["git", "-C", str(repo), "worktree", "add", "-q", "-b", f"hpfix/{g['slug']}", str(tree), "gh/dev"], repo)
    if code != 0:
        return {"slug": g["slug"], "error": "worktree", "detail": out[-300:]}
    if info.exists():
        shutil.rmtree(info)
    info.mkdir(parents=True)
    for b in g["bugs"]:
        for r in b["repros"]:
            shutil.copy(WORK / "r" / r["run"] / f"finding_{r['n']}.py", info / f"{b['id']}_claim_{r['k']}.py")
    (info / "spec.json").write_text(json.dumps({"repo": g["repo"], "file": g["file"], "test_file": g["test_file"],
                                                "bugs": [{"id": b["id"], "repros": b["repros"]} for b in g["bugs"]]}, indent=1))
    py = str(Path.home() / "Projects" / ("Puppetmaster" if g["repo"] == "Puppetmaster" else "marionette") / ".venv/bin/python")
    check = f"python3 {HERE / 'fix_check.py'} {info}"
    runner = f"python3 {HERE / 'guard.py'} run-locked tests -- {py} -m pytest -q -p no:cacheprovider -n 0 -x"
    fmt = dict(runner=runner, repo=g["repo"], n=len(g["bugs"]), file=g["file"], bugs=bug_text(g), info=info, test_file=g["test_file"], py=py,
               rules=RULES[g["repo"]], check=HERE / "fix_check.py")
    tools = ["Read", "Glob", "Grep", "Write", "Edit"] + [f"Bash({c}:*)" for c in (
        "cd", "ls", "pwd", "cat", "git diff", "git status", "git log", "git show", "git grep", "git blame", "grep", "rg", "wc", "head", "tail", "sed",
        "find", "python3", "sort", "uniq", "diff", "echo", "test", "mkdir", "timeout")]
    payload = {"allowed_tools": tools, "disallowed_tools": ["WebFetch", "WebSearch", "Task", "Agent", "NotebookEdit"]}
    graph = {"id": f"hp2-fix-{g['slug']}", "entry": "build",
             "defaults": {"adapter": "claude-code", "model": "claude-opus-5-5", "timeout_seconds": 5400, "finish": "criteria"},
             "nodes": [
                 {"id": "build", "kind": "agent", "role": "code", "files": (["puppetmaster/**", "tests/**"] if g["repo"] == "Puppetmaster" else ["harness/**", "pmharness/**", "tests/**"]), "task": BUILD.format(**fmt), "payload": payload},
                 {"id": "check", "kind": "shell", "command": check, "timeoutMs": 2700000},
                 {"id": "review", "kind": "judge", "model": "claude-sonnet-5-5", "task": JUDGE.format(**fmt), "payload": payload},
                 {"id": "done", "kind": "end", "status": "pass"},
                 {"id": "failed", "kind": "end", "status": "fail"}],
             "edges": [{"from": "build", "to": "check", "when": "ok"},
                       {"from": "check", "to": "review", "when": "ok"},
                       {"from": "check", "to": "build", "when": "fail", "max": 2},
                       {"from": "review", "to": "done", "when": "PASS"},
                       {"from": "review", "to": "build", "when": "FAIL", "max": 2},
                       {"from": "review", "to": "build", "when": "PARTIAL", "max": 1},
                       {"from": "review", "to": "done", "when": "PARTIAL"},
                       {"from": "check", "to": "failed"}, {"from": "build", "to": "failed"}, {"from": "review", "to": "failed"}]}
    gpath = WORK / "graphs" / f"hp2-fix-{g['slug']}.json"
    gpath.parent.mkdir(parents=True, exist_ok=True)
    gpath.write_text(json.dumps(graph, indent=1), encoding="utf-8")
    result: dict = {"slug": g["slug"], "repo": g["repo"], "file": g["file"], "bugs": [b["id"] for b in g["bugs"]], "tree": str(tree)}
    with guard.slot():
        _, out = sh(["puppetmaster", "flow", "run", str(gpath)], tree)
        try:
            run_id = parse_json(out)["run_id"]
        except Exception:
            result.update(error="launch", detail=out[-600:])
            return result
        _, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", "9000"], tree, timeout=9300)
    try:
        flow = parse_json(out)
    except Exception:
        result.update(error="wait", detail=out[-600:])
        return result
    steps, last = [], {}
    for s in flow.get("steps", []):
        item = {"node": s.get("node"), "ok": s.get("ok"), "verdict": s.get("verdict"), "reason": str(s.get("reason"))[:400]}
        if s.get("job_ids"):
            secs, cost = 0.0, 0.0
            for j in s["job_ids"]:
                a, b = job_record(j, tree)
                secs += a
                cost = max(cost, b)
            item.update(seconds=round(secs), cost_usd=round(cost - last.get(s["node"], 0.0), 3))
            last[s["node"]] = cost
        steps.append(item)
    _, check_out = sh(["python3", str(HERE / "fix_check.py"), str(info)], tree, timeout=2700)
    _, diffstat = sh(["git", "diff", "--stat"], tree)
    result.update(flow=run_id, flow_status=flow.get("status"), steps=steps, check=check_out[-600:], diffstat=diffstat[-600:],
                  cost_usd=round(sum(s.get("cost_usd") or 0 for s in steps), 2), seconds=sum(s.get("seconds") or 0 for s in steps))
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=["plan", "run"])
    parser.add_argument("--only", nargs="*", default=[])
    parser.add_argument("--concurrency", type=int, default=8)
    args = parser.parse_args()
    groups = plan()
    if args.cmd == "plan":
        print(json.dumps([{"slug": g["slug"], "bugs": len(g["bugs"]), "test_file": g["test_file"]} for g in groups], indent=1))
        return 0
    todo = [g for g in groups if not args.only or g["slug"] in args.only]
    with ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        results = list(pool.map(one, todo))
    path = HERE / "fix_runs.json"
    old = json.loads(path.read_text()) if path.exists() else []
    done = {r["slug"] for r in results}
    path.write_text(json.dumps([r for r in old if r["slug"] not in done] + results, indent=1) + "\n", encoding="utf-8")
    print(json.dumps([{k: r.get(k) for k in ("slug", "flow_status", "cost_usd", "seconds", "error")} | {"steps": [(s["node"], s.get("verdict") or s.get("ok")) for s in r.get("steps", [])]} for r in results], indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
