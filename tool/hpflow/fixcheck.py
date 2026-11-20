"""The script check after a fix worker. Run it in the worktree of the fix.

    python3 -m hpflow.fixcheck INFO_DIR

1. Each changed file must be in the write scope of the fix.
2. Each repro of a confirmed bug must give a result that is different from the result before the fix.
3. The new test file must pass.
4. The tests of the repository that name the changed module must pass.
"""
from __future__ import annotations

import ast
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

from .common import UsageError, git_status, project_python, repro_state, run_group, run_snippet, shell_quote

MAX_RELATED_BYTES = 400_000
# The number of related test files in one test command.
RELATED_PART = 12
# Files that a test run leaves. They are not a change of the worker.
CACHE_PARTS = ("__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache")


def changed_files(tree: Path) -> Optional[List[str]]:
    """Each path that differs from the commit of the worktree: changed, added, deleted, renamed or new.
    None when git cannot read the status of the worktree.

    The list has no bytecode file and no file of a cache folder (`CACHE_PARTS`), tracked or not: a test run
    writes them, so they are not a change of the worker."""
    entries = git_status(tree)
    if entries is None:
        return None
    paths: List[str] = []
    for entry in entries:
        paths += [p for p in (entry["path"], entry["source"]) if p]
    return [p for p in paths if not (set(Path(p).parts) & set(CACHE_PARTS)) and not p.endswith(".pyc")]


def in_scope(path: str, scope: List[str]) -> bool:
    for entry in scope:
        if entry.endswith("/**"):
            if path.startswith(entry[:-2]):
                return True
        elif path == entry:
            return True
    return False


def out_of_scope(tree: Path, scope: List[str]) -> Optional[List[str]]:
    """The changed paths that are not in the write scope. None when git cannot read the status of the worktree."""
    changed = changed_files(tree)
    return None if changed is None else sorted(p for p in changed if not in_scope(p, scope))


def module_name(file: str) -> str:
    """The name that a test uses for the module of a file: the stem, or for `pkg/__init__.py` the package `pkg`.
    Empty when the file is an `__init__.py` with no folder."""
    path = Path(file)
    return path.parent.name if path.stem == "__init__" else path.stem


def imports_module(source: str, stem: str) -> bool:
    """True when a test file imports the module `stem` in any form: `import mod`, `import pkg.mod`,
    `from pkg.mod import f`, `from mod import f`, `from pkg import a, mod`, with or without `as`.

    The Python parser reads the imports, so the form of the line does not matter. A file that does not parse
    has no import that Python can run, so it is not related."""
    try:
        tree = ast.parse(source)
    except (SyntaxError, ValueError):
        return False
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            if any(stem in alias.name.split(".") for alias in node.names):
                return True
        elif isinstance(node, ast.ImportFrom):
            if stem in (node.module or "").split(".") or any(alias.name == stem for alias in node.names):
                return True
    return False


def test_command(spec: Dict[str, Any], tests: List[str]) -> str:
    return spec["test_cmd"].format(python=shell_quote(spec["python"]), tests=" ".join(shell_quote(t) for t in tests))


def run_tests(spec: Dict[str, Any], tree: Path, tests: List[str], timeout: int) -> subprocess.CompletedProcess:
    code, out, err = run_group(test_command(spec, tests), tree, timeout, shell=True)
    if code is None:
        return subprocess.CompletedProcess(tests, 124, out, err + f"\nthe tests did not end in {timeout} seconds")
    return subprocess.CompletedProcess(tests, code, out, err)


def check(info: Path, tree: Path) -> Dict[str, Any]:
    spec = json.loads((info / "spec.json").read_text(encoding="utf-8"))
    try:
        python = project_python(spec.get("python"))
    except UsageError as e:
        # With no Python of the project, no repro and no test can run, so nothing shows that the fix is good.
        return {"verdict": "reject", "problems": [str(e)], "large_test_files_not_run": []}
    problems = []
    skipped: List[str] = []
    stray = out_of_scope(tree, spec["scope"]) if spec.get("scope") else []
    if stray is None:
        # No list of the changed files is no proof that the change stays in its scope.
        problems.append("git status failed in the worktree, so the check of the write scope did not run")
    elif stray:
        problems.append("the change touches files outside the write scope (" + ", ".join(spec["scope"]) + "): "
                        + ", ".join(stray[:20]) + ". Put these files back as they were, or delete the new ones")
    for b in spec["bugs"]:
        for r in b["repros"]:
            got = run_snippet(tree, info / r["file"], info / "home", python, import_root=spec.get("import_root") or "")
            state = repro_state(got, r["result_now"])
            if state == "same":
                problems.append(f"bug {b['id']}: the repro {r['file']} still gives the old result {r['result_now']!r}")
            elif state == "unknown":
                # The release gate does not close a bug on such a repro, so the check does not accept the fix.
                problems.append(f"bug {b['id']}: the repro {r['file']} does not run after the change "
                                f"({got.get('error')}: {str(got.get('message'))[:200]}). Keep the names that the repro uses")
    test_file = tree / spec["test_file"]
    if not test_file.exists():
        problems.append(f"the test file {spec['test_file']} does not exist")
    else:
        p = run_tests(spec, tree, [spec["test_file"]], 900)
        if p.returncode != 0:
            problems.append("the new test file fails:\n" + (p.stdout + p.stderr)[-1500:])
        stem = module_name(spec["file"])
        related = []
        tests_dir = tree / (spec.get("tests_dir") or "tests")
        if tests_dir.is_dir():
            # A file named *_test.py is a test file too (see common.is_test_file).
            for t in sorted(set(tests_dir.rglob("test_*.py")) | set(tests_dir.rglob("*_test.py"))):
                if t == test_file:
                    continue
                if stem and (stem in t.name or imports_module(t.read_text(encoding="utf-8", errors="replace"), stem)):
                    if t.stat().st_size > MAX_RELATED_BYTES:
                        # A very large test file can run for a long time. The CI of the repository runs it.
                        skipped.append(t.relative_to(tree).as_posix())
                        continue
                    related.append(t.relative_to(tree).as_posix())
        # Each related test file runs. The parts keep a command line below the limit of the Windows shell.
        for start in range(0, len(related), RELATED_PART):
            p = run_tests(spec, tree, related[start:start + RELATED_PART], 1500)
            if p.returncode != 0:
                problems.append("tests of the repository fail after the change:\n" + (p.stdout + p.stderr)[-2000:])
                break
    return {"verdict": "accept" if not problems else "reject", "problems": problems, "large_test_files_not_run": skipped}


def main() -> int:
    result = check(Path(sys.argv[1]), Path.cwd())
    print(json.dumps(result, indent=1))
    return 0 if result["verdict"] == "accept" else 1


if __name__ == "__main__":
    sys.exit(main())
