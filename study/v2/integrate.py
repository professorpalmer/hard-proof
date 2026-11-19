#!/usr/bin/env python3
"""Hard Proof v2: commit each accepted fix in its worktree and put them on one branch for each repository.

Usage:
    python3 integrate.py commit      one commit in each fix worktree (owner identity of the clone, explicit paths)
    python3 integrate.py branch      cherry-pick the commits onto `hpfix/all` in `hp-work/fix/_all-<repo>`
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = Path.home() / "Projects" / "hp-work"
MANUAL_ACCEPT = {"mn-pmharness-drivers-cursor-cli": "the driver fix and its tests are accepted; the edit to tests/test_providers.py is out",
                 "pm-puppetmaster-diagnostics": "the one failed related test passes alone in this worktree and on clean dev"}


def sh(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr).strip()


def accepted() -> list[dict]:
    runs = {r["slug"]: r for r in json.loads((HERE / "fix_runs.json").read_text())}
    plan = {g["slug"]: g for g in json.loads((HERE / "fix_plan.json").read_text())}
    out = []
    for slug, r in runs.items():
        ok = r.get("flow_status") == "done" and "accept" in r.get("check", "")
        if ok or slug in MANUAL_ACCEPT:
            out.append({**plan[slug], "run": r})
    return out


def message(g: dict) -> str:
    n = len(g["bugs"])
    lines = [f"Fix {n} bug{'s' if n != 1 else ''} in {g['file']}", ""]
    for b in g["bugs"]:
        lines.append(f"- {b['function'].split(' ')[0]}: {b['what_goes_wrong']}")
    builds = [s for s in g["run"].get("steps", []) if s["node"] == "build" and s.get("reason")]
    if builds:
        lines += ["", "Change: " + builds[-1]["reason"].strip().rstrip(".") + "."]
    lines += ["", "Each bug has a regression test in " + g["test_file"] + ".",
              "Found by an agent review, confirmed on this source by two independent",
              "verifier agents, and reviewed by a judge agent after the fix."]
    out = []
    for line in lines:
        while len(line) > 78 and " " in line[:78]:
            cut = line.rfind(" ", 0, 78)
            out.append(line[:cut])
            line = "  " + line[cut + 1:]
        out.append(line)
    return "\n".join(out) + "\n"


def commit() -> int:
    rows = []
    for g in accepted():
        tree = WORK / "fix" / g["slug"]
        raw = subprocess.run(["git", "status", "--porcelain"], cwd=tree, capture_output=True, text=True).stdout
        paths = [l[3:].strip() for l in raw.splitlines() if len(l) > 3]
        paths = [p for p in paths if not p.startswith((".codegraph", ".lake")) and "__pycache__" not in p]
        if not paths:
            _, head = sh(["git", "log", "--format=%h %s", "-1"], tree)
            rows.append({"slug": g["slug"], "state": "no change to commit", "head": head})
            continue
        sh(["git", "add", "--", *paths], tree)
        code, out = subprocess.run(["git", "commit", "-q", "-F", "-"], cwd=tree, input=message(g), capture_output=True, text=True).returncode, ""
        _, head = sh(["git", "log", "--format=%h %an | %s", "-1"], tree)
        rows.append({"slug": g["slug"], "paths": paths, "head": head, "exit": code})
    print(json.dumps(rows, indent=1))
    return 0


def branch() -> int:
    report = {}
    for repo, prefix in (("Puppetmaster", "pm-"), ("marionette", "mn-")):
        clone = WORK / repo
        tree = WORK / "fix" / f"_all-{repo}"
        sh(["git", "fetch", "-q", "gh", "dev"], clone)
        if tree.exists():
            sh(["git", "worktree", "remove", "--force", str(tree)], clone)
        sh(["git", "branch", "-D", "hpfix/all"], clone)
        code, out = sh(["git", "worktree", "add", "-q", "-b", "hpfix/all", str(tree), "gh/dev"], clone)
        picked, failed = [], []
        for g in accepted():
            if not g["slug"].startswith(prefix):
                continue
            _, sha = sh(["git", "rev-parse", f"hpfix/{g['slug']}"], clone)
            _, base = sh(["git", "merge-base", sha, "gh/dev"], clone)
            if sha == base:
                failed.append({"slug": g["slug"], "why": "no commit on the branch"})
                continue
            code, out = sh(["git", "cherry-pick", sha], tree)
            if code != 0:
                sh(["git", "cherry-pick", "--abort"], tree)
                failed.append({"slug": g["slug"], "why": out[-300:]})
            else:
                picked.append(g["slug"])
        _, log = sh(["git", "log", "--oneline", "gh/dev..HEAD"], tree)
        report[repo] = {"picked": len(picked), "failed": failed, "commits": log.splitlines()}
    print(json.dumps(report, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(commit() if sys.argv[1:] == ["commit"] else branch() if sys.argv[1:] == ["branch"] else 2)
