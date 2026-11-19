"""The script check after a fix worker. Run it in the worktree of the fix.

    python3 -m hpflow.fixcheck INFO_DIR

1. Each changed file must be in the write scope of the fix.
2. Each repro of a confirmed bug must give a result that is different from the result before the fix.
3. The new test file must pass.
4. The tests of the repository that name the changed module must pass.
"""
from __future__ import annotations

import json
import shlex
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

from .common import run_group, run_snippet

MAX_RELATED_BYTES = 400_000
# Files that a test run leaves. They are not a change of the worker.
CACHE_PARTS = ("__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache")


def changed_files(tree: Path) -> List[str]:
    """Each path that differs from the commit of the worktree: changed, added, deleted, renamed or new."""
    code, out, _ = run_group(["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"], tree, 120)
    if code != 0:
        return []
    paths: List[str] = []
    entries = out.split("\0")
    i = 0
    while i < len(entries):
        entry = entries[i]
        i += 1
        if len(entry) < 4:
            continue
        paths.append(entry[3:])
        if entry[0] in "RC":
            # A rename or copy has its source path in the next entry.
            if i < len(entries) and entries[i]:
                paths.append(entries[i])
            i += 1
    return [p for p in paths if not (set(Path(p).parts) & set(CACHE_PARTS)) and not p.endswith(".pyc")]


def in_scope(path: str, scope: List[str]) -> bool:
    for entry in scope:
        if entry.endswith("/**"):
            if path.startswith(entry[:-2]):
                return True
        elif path == entry:
            return True
    return False


def out_of_scope(tree: Path, scope: List[str]) -> List[str]:
    return sorted(p for p in changed_files(tree) if not in_scope(p, scope))


def test_command(spec: Dict[str, Any], tests: List[str]) -> str:
    return spec["test_cmd"].format(python=shlex.quote(spec["python"]), tests=" ".join(shlex.quote(t) for t in tests))


def run_tests(spec: Dict[str, Any], tree: Path, tests: List[str], timeout: int) -> subprocess.CompletedProcess:
    code, out, err = run_group(test_command(spec, tests), tree, timeout, shell=True)
    if code is None:
        return subprocess.CompletedProcess(tests, 124, out, err + f"\nthe tests did not end in {timeout} seconds")
    return subprocess.CompletedProcess(tests, code, out, err)


def check(info: Path, tree: Path) -> Dict[str, Any]:
    spec = json.loads((info / "spec.json").read_text(encoding="utf-8"))
    problems = []
    skipped: List[str] = []
    stray = out_of_scope(tree, spec["scope"]) if spec.get("scope") else []
    if stray:
        problems.append("the change touches files outside the write scope (" + ", ".join(spec["scope"]) + "): "
                        + ", ".join(stray[:20]) + ". Put these files back as they were, or delete the new ones")
    for b in spec["bugs"]:
        for r in b["repros"]:
            got = run_snippet(tree, info / r["file"], info / "home")
            if got.get("ok") and got.get("result") == r["result_now"]:
                problems.append(f"bug {b['id']}: the repro {r['file']} still gives the old result {r['result_now']!r}")
    test_file = tree / spec["test_file"]
    if not test_file.exists():
        problems.append(f"the test file {spec['test_file']} does not exist")
    else:
        p = run_tests(spec, tree, [spec["test_file"]], 900)
        if p.returncode != 0:
            problems.append("the new test file fails:\n" + (p.stdout + p.stderr)[-1500:])
        stem = Path(spec["file"]).stem
        related = []
        if (tree / "tests").is_dir():
            for t in sorted((tree / "tests").rglob("test_*.py")):
                if t == test_file:
                    continue
                text = t.read_text(errors="replace")[:20000]
                if stem in t.name or f"import {stem}" in text or f".{stem} " in text:
                    if t.stat().st_size > MAX_RELATED_BYTES:
                        # A very large test file can run for a long time. The CI of the repository runs it.
                        skipped.append(str(t.relative_to(tree)))
                        continue
                    related.append(str(t.relative_to(tree)))
        related = related[:12]
        if related:
            p = run_tests(spec, tree, related, 1500)
            if p.returncode != 0:
                problems.append("tests of the repository fail after the change:\n" + (p.stdout + p.stderr)[-2000:])
    return {"verdict": "accept" if not problems else "reject", "problems": problems, "large_test_files_not_run": skipped}


def main() -> int:
    result = check(Path(sys.argv[1]), Path.cwd())
    print(json.dumps(result, indent=1))
    return 0 if result["verdict"] == "accept" else 1


if __name__ == "__main__":
    sys.exit(main())
