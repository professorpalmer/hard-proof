"""The script check after a fix worker. Run it in the worktree of the fix.

    python3 -m hpflow.fixcheck INFO_DIR

1. Each repro of a confirmed bug must give a result that is different from the result before the fix.
2. The new test file must pass.
3. The tests of the repository that name the changed module must pass.
"""
from __future__ import annotations

import json
import shlex
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

from .common import run_group, run_snippet


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
                    related.append(str(t.relative_to(tree)))
        related = related[:12]
        if related:
            p = run_tests(spec, tree, related, 1500)
            if p.returncode != 0:
                problems.append("tests of the repository fail after the change:\n" + (p.stdout + p.stderr)[-2000:])
    return {"verdict": "accept" if not problems else "reject", "problems": problems}


def main() -> int:
    result = check(Path(sys.argv[1]), Path.cwd())
    print(json.dumps(result, indent=1))
    return 0 if result["verdict"] == "accept" else 1


if __name__ == "__main__":
    sys.exit(main())
