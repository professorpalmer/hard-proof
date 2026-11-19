#!/usr/bin/env python3
"""Hard Proof v2: the check after a fix worker. Run in the worktree of the fix.

    python3 fix_check.py INFO_DIR

1. Each repro of a confirmed bug must give a result that is different from the result before the fix.
2. The new test file must pass.
3. The tests of the repository that name the changed module must pass.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bugs import run_snippet  # noqa: E402

PY = {"Puppetmaster": str(Path.home() / "Projects/Puppetmaster/.venv/bin/python"),
      "marionette": str(Path.home() / "Projects/marionette/.venv/bin/python")}


def main() -> int:
    info = Path(sys.argv[1])
    spec = json.loads((info / "spec.json").read_text())
    tree = Path.cwd()
    problems = []
    for b in spec["bugs"]:
        for r in b["repros"]:
            got = run_snippet(tree, info / f"{b['id']}_claim_{r['k']}.py")
            if got.get("ok") and got.get("result") == r["result_now"]:
                problems.append(f"bug {b['id']}: the repro {b['id']}_claim_{r['k']}.py still gives the old result {r['result_now']!r}")
    test_file = tree / spec["test_file"]
    if not test_file.exists():
        problems.append(f"the test file {spec['test_file']} does not exist")
    else:
        py = PY[spec["repo"]]
        lock = [sys.executable, str(Path(__file__).resolve().parent / "guard.py"), "run-locked", "tests", "--"]
        p = subprocess.run(lock + [py, "-m", "pytest", "-q", "-p", "no:cacheprovider", "-n", "0", "-x", spec["test_file"]], capture_output=True, text=True, timeout=3600)
        if p.returncode != 0:
            problems.append("the new test file fails:\n" + (p.stdout + p.stderr)[-1500:])
        stem = Path(spec["file"]).stem
        related = sorted({str(t.relative_to(tree)) for t in (tree / "tests").glob("test_*.py")
                          if t != test_file and (stem in t.name or f"import {stem}" in t.read_text(errors="replace")[:20000]
                                                 or f".{stem} " in t.read_text(errors="replace")[:20000])})[:12]
        if related:
            p = subprocess.run(lock + [py, "-m", "pytest", "-q", "-p", "no:cacheprovider", "-n", "0", "-x", *related], capture_output=True, text=True, timeout=5400)
            if p.returncode != 0:
                problems.append("tests of the repository fail after the change:\n" + (p.stdout + p.stderr)[-2000:])
    print(json.dumps({"verdict": "accept" if not problems else "reject", "problems": problems}, indent=1))
    return 0 if not problems else 1


if __name__ == "__main__":
    sys.exit(main())
