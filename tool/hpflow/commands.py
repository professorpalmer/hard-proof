"""The commands of hpflow. Each one reads and writes JSON files in the audit folder."""
from __future__ import annotations

import ast
import re
import shlex
import shutil
import sys
import threading
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

from . import briefs
from .common import (COST_NOTE, DEFAULT_CONCURRENCY, LEAN_ARGS, MISSING, TOOL_DIR, StepError, UsageError, copy_tree, digest, git, is_test_file, model_id,
                     read_json, run_snippet, sh, write_json)
from .fixcheck import check as fix_check
from .runner import Runner, agent_graph

DEFAULT_TEST_CMD = "{python} -m pytest -q -p no:cacheprovider {tests}"
EXTRA_PATHS = ("tests", "docs", "README.md", "pyproject.toml")


class Context:
    """The audit folder, the runner and the shared options of one call."""

    def __init__(self, out: Path, runner: Runner, redo: bool = False, concurrency: int = DEFAULT_CONCURRENCY,
                 lean: bool = True):
        self.lean = lean
        self.out = out.resolve()
        self.runner = runner
        self.redo = redo
        self.concurrency = max(1, concurrency)
        self.lock = threading.Lock()

    @property
    def src(self) -> Path:
        return self.out / "src"

    @property
    def home(self) -> Path:
        return self.out / "home"

    def audit(self) -> Dict[str, Any]:
        a = read_json(self.out / "audit.json")
        if not a:
            raise UsageError(f"no audit in {self.out}: run `init` first")
        return a

    def record_path(self, rid: str) -> Path:
        return self.out / "records" / f"{rid}.json"

    def stored(self, rid: str) -> Optional[Dict[str, Any]]:
        """A stored worker result, or None when the run must happen (no record, an error record, or --redo)."""
        if self.redo:
            return None
        r = read_json(self.record_path(rid))
        if not r or r.get("error"):
            return None
        return r

    def save(self, rid: str, record: Dict[str, Any]) -> None:
        with self.lock:
            write_json(self.record_path(rid), record)


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def pool_map(ctx: Context, fn: Callable[[Any], Any], items: List[Any]) -> List[Any]:
    if not items:
        return []
    with ThreadPoolExecutor(max_workers=ctx.concurrency) as pool:
        return list(pool.map(fn, items))


def costs(records: List[Dict[str, Any]]) -> Dict[str, Any]:
    return {"cost_usd_api_equivalent": round(sum(r.get("cost_usd") or 0 for r in records), 4),
            "seconds": round(sum(r.get("seconds") or 0 for r in records)), "cost_note": COST_NOTE}


# ---------------------------------------------------------------- init

def cmd_init(ctx: Context, repo: str, ref: str, paths: Optional[List[str]], python: Optional[str],
             test_cmd: Optional[str]) -> Dict[str, Any]:
    root = Path(repo).expanduser().resolve()
    code, top = git(root, "rev-parse", "--show-toplevel")
    if code != 0:
        raise UsageError(f"{root} is not a git repository")
    root = Path(top.strip())
    code, commit = git(root, "rev-parse", "--verify", f"{ref}^{{commit}}")
    if code != 0:
        raise UsageError(f"the ref {ref} is not a commit of {root}")
    commit = commit.strip()

    def present(p: str) -> bool:
        return git(root, "cat-file", "-e", f"{commit}:{p}")[0] == 0

    if paths:
        missing = [p for p in paths if not present(p.rstrip("/"))]
        if missing:
            raise UsageError(f"these paths are not in {commit[:12]}: {', '.join(missing)}")
        paths = [p.rstrip("/") for p in paths]
    else:
        _, listing = git(root, "ls-tree", "--name-only", "-d", commit)
        paths = [d for d in listing.split() if d not in EXTRA_PATHS and present(f"{d}/__init__.py")]
        paths += [p for p in EXTRA_PATHS if present(p)]
        if not paths:
            raise UsageError("no package folder (a top-level folder with __init__.py) found: give --paths")
    if python is None:
        venv = root / ".venv" / "bin" / "python"
        python = str(venv) if venv.exists() else sys.executable
    old = read_json(ctx.out / "audit.json")
    if old and old.get("commit") != commit and not ctx.redo:
        raise UsageError(f"{ctx.out} holds an audit of {old.get('commit', '')[:12]}: use a new --out or --redo")
    audit = {"repo": str(root), "ref": ref, "commit": commit, "paths": paths, "python": python,
             "test_cmd": test_cmd or DEFAULT_TEST_CMD, "created": (old or {}).get("created") or now()}
    snapshot = "kept"
    if ctx.redo or not old or old.get("paths") != paths or not ctx.src.is_dir():
        if ctx.src.exists():
            shutil.rmtree(ctx.src)
        ctx.src.mkdir(parents=True)
        tarball = ctx.out / "src.tar"
        code, detail = git(root, "archive", "-o", str(tarball), commit, *paths)
        if code == 0:
            code, detail = sh(["tar", "-x", "-f", str(tarball), "-C", str(ctx.src)])
        tarball.unlink(missing_ok=True)
        if code != 0:
            raise StepError(f"git archive failed: {detail[-300:]}")
        snapshot = "written"
    write_json(ctx.out / "audit.json", audit)
    return {"command": "init", "ok": True, "audit": audit, "snapshot": snapshot, "src": str(ctx.src)}


# ---------------------------------------------------------------- targets

def functions_of(source: str) -> List[Dict[str, Any]]:
    """The functions and methods of a module: qualified name, first line (decorators included), last line."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    out: List[Dict[str, Any]] = []

    def walk(body: List[ast.stmt], prefix: str) -> None:
        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                start = min([node.lineno] + [d.lineno for d in node.decorator_list])
                out.append({"function": prefix + node.name, "start": start, "end": node.end_lineno or node.lineno})
            elif isinstance(node, ast.ClassDef):
                walk(node.body, prefix + node.name + ".")

    walk(tree.body, "")
    return out


def parse_diff(text: str) -> List[Dict[str, Any]]:
    """Files of a `git diff -U0`, each with the old and new path and the line ranges of its hunks."""
    files: List[Dict[str, Any]] = []
    cur: Optional[Dict[str, Any]] = None
    hunk = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")
    for line in text.splitlines():
        if line.startswith("diff --git "):
            cur = {"old": None, "new": None, "old_ranges": [], "new_ranges": []}
            files.append(cur)
        elif cur is None:
            continue
        elif line.startswith("--- "):
            cur["old"] = None if line[4:] == "/dev/null" else line[4:][2:]
        elif line.startswith("+++ "):
            cur["new"] = None if line[4:] == "/dev/null" else line[4:][2:]
        else:
            m = hunk.match(line)
            if m:
                for (s, c), key in (((m.group(1), m.group(2)), "old_ranges"), ((m.group(3), m.group(4)), "new_ranges")):
                    start, count = int(s), 1 if c is None else int(c)
                    cur[key].append((start, start + count - 1) if count else (start, start + 1))
    return files


def overlaps(fn: Dict[str, Any], ranges: List[Tuple[int, int]]) -> bool:
    return any(a <= fn["end"] and fn["start"] <= b for a, b in ranges)


def top_of(file: str) -> str:
    parts = Path(file).parts
    return parts[0] if len(parts) > 1 else Path(file).stem


def make_target(file: str, fn: Dict[str, Any], how: str) -> Dict[str, Any]:
    return {"id": digest("target", file, fn["function"]), "file": file, "function": fn["function"], "top": top_of(file),
            "lines": [fn["start"], fn["end"]], "length": fn["end"] - fn["start"] + 1, "source": how}


def in_paths(file: str, paths: List[str]) -> bool:
    return any(file == p or file.startswith(p.rstrip("/") + "/") for p in paths)


def cmd_targets(ctx: Context, changed: Optional[str], functions: Optional[List[str]], files: Optional[List[str]],
                max_lines: int, max_n: Optional[int]) -> Dict[str, Any]:
    audit = ctx.audit()
    repo = Path(audit["repo"])
    candidates: List[Dict[str, Any]] = []
    skipped: List[Dict[str, Any]] = []
    if changed:
        if ".." not in changed or "..." in changed:
            raise UsageError("--changed takes A..B")
        a, b = changed.split("..", 1)
        b = b or "HEAD"
        for ref in (a, b):
            if git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}")[0] != 0:
                raise UsageError(f"the ref {ref} is not a commit of {repo}")
        code, diff = git(repo, "diff", "-U0", "--no-color", "--no-ext-diff", a, b, "--", *audit["paths"])
        if code != 0:
            raise StepError(f"git diff failed: {diff[-300:]}")
        for f in parse_diff(diff):
            path = f["new"] or f["old"]
            if not path or not path.endswith(".py") or not in_paths(path, audit["paths"]):
                continue
            new_fns = functions_of(git(repo, "show", f"{b}:{f['new']}")[1]) if f["new"] else []
            old_fns = functions_of(git(repo, "show", f"{a}:{f['old']}")[1]) if f["old"] else []
            if is_test_file(path):
                hit = [fn for fn in new_fns if overlaps(fn, f["new_ranges"])]
                for fn in hit:
                    skipped.append({"file": path, "function": fn["function"], "reason": "test file"})
                if not hit:
                    skipped.append({"file": path, "function": None, "reason": "test file"})
                continue
            names = {fn["function"] for fn in new_fns}
            for fn in old_fns:
                if fn["function"] not in names and (f["new"] is None or overlaps(fn, f["old_ranges"])):
                    skipped.append({"file": path, "function": fn["function"], "reason": "removed"})
            for fn in new_fns:
                if overlaps(fn, f["new_ranges"]):
                    candidates.append(make_target(f["new"], fn, "changed"))
    else:
        wanted: List[Tuple[str, Optional[str]]] = []
        for spec in functions or []:
            if ":" not in spec:
                raise UsageError(f"--function takes FILE:NAME, not {spec}")
            file, name = spec.rsplit(":", 1)
            wanted.append((file, name))
        wanted += [(file, None) for file in files or []]
        for file, name in wanted:
            path = ctx.src / file
            if not path.is_file():
                raise UsageError(f"{file} is not in the snapshot {ctx.src}")
            fns = functions_of(path.read_text(encoding="utf-8", errors="replace"))
            if name is not None:
                fns = [fn for fn in fns if fn["function"] == name]
                if not fns:
                    raise UsageError(f"no function {name} in {file}")
            for fn in fns:
                candidates.append(make_target(file, fn, "function" if name else "file"))
    seen, targets = set(), []
    for t in sorted(candidates, key=lambda t: (t["file"], t["lines"][0])):
        if t["id"] in seen:
            continue
        seen.add(t["id"])
        if t["length"] > max_lines:
            skipped.append({"file": t["file"], "function": t["function"],
                            "reason": f"too long ({t['length']} lines, the limit is {max_lines})"})
        elif max_n is not None and len(targets) >= max_n:
            skipped.append({"file": t["file"], "function": t["function"], "reason": f"over --max {max_n}"})
        else:
            targets.append(t)
    data = {"mode": "changed" if changed else "named", "changed": changed, "max_lines": max_lines, "targets": targets,
            "skipped": skipped}
    write_json(ctx.out / "targets.json", data)
    return {"command": "targets", "ok": True, "targets": [f"{t['file']}:{t['function']}" for t in targets],
            "skipped": skipped}


# ---------------------------------------------------------------- review

def prepare_folder(ctx: Context, folder: Path) -> None:
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir(parents=True)
    copy_tree(ctx.src, folder / "project")


def review_groups(targets: List[Dict[str, Any]], group: str, group_size: int) -> List[List[Dict[str, Any]]]:
    """The targets of one reviewer session: one function, or the functions of one file in parts of `group_size`."""
    if group == "function":
        return [[t] for t in targets]
    by_file: Dict[str, List[Dict[str, Any]]] = {}
    for t in targets:
        by_file.setdefault(t["file"], []).append(t)
    out: List[List[Dict[str, Any]]] = []
    for ts in by_file.values():
        ts = sorted(ts, key=lambda t: t["lines"][0])
        out += [ts[i:i + group_size] for i in range(0, len(ts), group_size)]
    return out


def cmd_review(ctx: Context, model: str, shell: bool, passes: int, repro_timeout: float, group: str = "function",
               group_size: int = 6) -> Dict[str, Any]:
    audit = ctx.audit()
    targets = (read_json(ctx.out / "targets.json") or {}).get("targets")
    if targets is None:
        raise UsageError("no targets.json: run `targets` first")
    arm = "shell" if shell else "plain"
    jobs = [(ts, p) for ts in review_groups(targets, group, group_size) for p in range(1, passes + 1)]

    def one(job: Tuple[List[Dict[str, Any]], int]) -> Tuple[Dict[str, Any], bool]:
        ts, p = job
        t = ts[0]
        single = group == "function"
        rid = (digest("review", audit["commit"], t["id"], p, model_id(model), arm) if single
               else digest("review", audit["commit"], "file", *[x["id"] for x in ts], p, model_id(model), arm))
        r = ctx.stored(rid)
        if r:
            return r, False
        folder = ctx.out / "runs" / rid
        prepare_folder(ctx, folder)
        if single:
            task = briefs.REVIEW.format(function=t["function"], file=t["file"], top=t["top"], arm_text=briefs.REVIEW_ARM[arm])
            check = briefs.REVIEW_CHECK
        else:
            write_json(folder / "functions.json", [x["function"] for x in ts])
            task = briefs.REVIEW_FILE.format(functions="\n".join(f"- `{x['function']}`" for x in ts), file=t["file"], top=t["top"],
                                             per_function=briefs.PER_FUNCTION, arm_text=briefs.REVIEW_ARM[arm])
            check = briefs.REVIEW_FILE_CHECK
        graph = agent_graph(f"hpf-{rid}", task, ["findings.json", "finding_*.py"], model, shell=shell, check=check, timeout=2400,
                            lean=ctx.lean)
        r = ctx.runner.run(graph, folder)
        r.update(kind="review", run=rid, folder=str(folder), target=t["id"], targets=[x["id"] for x in ts], pass_n=p,
                 model=model_id(model), arm=arm, finished=now())
        ctx.save(rid, r)
        return r, True

    results = pool_map(ctx, one, jobs)
    records = [r for r, _ in results]
    findings: List[Dict[str, Any]] = []
    by_id = {t["id"]: t for t in targets}

    def gate(r: Dict[str, Any]) -> List[Dict[str, Any]]:
        folder = Path(r["folder"])
        items = read_json(folder / "findings.json")
        if not isinstance(items, list):
            r["note"] = "no valid findings.json"
            return []
        out = []
        mine = [by_id[i] for i in (r.get("targets") or [r["target"]])]
        by_name = {t["function"]: t for t in mine}
        seen: Dict[str, int] = {}
        for i, f in enumerate(items[:5] if len(mine) == 1 else items):
            if not isinstance(f, dict):
                continue
            n = f.get("n", i + 1)
            t = mine[0] if len(mine) == 1 else by_name.get(str(f.get("function")))
            if t is None:
                r["note_unknown_function"] = f"finding {n} names a function that is not in the list"
                continue
            seen[t["id"]] = seen.get(t["id"], 0) + 1
            if len(mine) > 1 and seen[t["id"]] > briefs.PER_FUNCTION:
                continue
            row = {"id": f"{r['run']}-{n}", "run": r["run"], "n": n, "target": t["id"], "file": t["file"],
                   "function": t["function"], "model": r["model"], "claim": str(f.get("claim"))[:600],
                   "expected": str(f.get("expected"))[:300], "confidence": f.get("confidence"),
                   "repro": str(folder / f"finding_{n}.py")}
            snippet = folder / f"finding_{n}.py"
            if not snippet.exists():
                row.update(grade=0, reason="no repro file")
            else:
                got = run_snippet(ctx.src, snippet, ctx.home, timeout=repro_timeout)
                row["run_result"] = got
                if got.get("ok"):
                    row.update(grade=1, result=got["result"])
                elif got.get("error") == "timeout":
                    row.update(grade=0, reason=f"the repro timed out ({repro_timeout} seconds)")
                elif got.get("error") in ("ImportError", "ModuleNotFoundError", "AttributeError", "NameError"):
                    row.update(grade=0, reason=f"the repro cannot import the function: {got.get('error')}: {got.get('message')}")
                else:
                    row.update(grade=0, reason=f"run() raised {got.get('error')}: {got.get('message')}")
            out.append(row)
        return out

    for rows in pool_map(ctx, gate, records):
        findings.extend(rows)
    write_json(ctx.out / "review.json", {"model": model_id(model), "arm": arm, "passes": passes, "group": group,
                                         "runs": [r["run"] for r in records], "findings": findings})
    failed = [{"run": r["run"], "target": r["target"], "error": r.get("error") or r.get("note") or r.get("status")}
              for r in records if r.get("error") or r.get("note")]
    report = {"command": "review", "ok": not failed, "runs": len(records), "worker_runs": sum(1 for _, n in results if n),
              "reused": sum(1 for _, n in results if not n), "group": group, "findings": len(findings),
              "grade_1": sum(1 for f in findings if f["grade"] == 1),
              "grade_0": [{"id": f["id"], "reason": f["reason"]} for f in findings if f["grade"] == 0],
              "failed_runs": failed}
    report.update(costs(records))
    return report


# ---------------------------------------------------------------- verify

SINGLE_CLASS = {"real_unreachable": "real_unreachable", "intended": "by_design"}


def verdict_class(verdicts: Dict[str, Optional[str]], need: int, staged: bool = False) -> str:
    vals = list(verdicts.values())
    if staged and vals and vals[0] not in (None, "real") and all(v is None for v in vals[1:]):
        # The first verifier did not say `real`, so the claim cannot be confirmed, and the others did not run.
        return SINGLE_CLASS.get(vals[0], "mixed")
    if len(vals) < need or any(v is None for v in vals):
        return "mixed"
    if all(v == "real" for v in vals):
        return "confirmed"
    if all(v in ("real", "real_unreachable") for v in vals):
        return "real_unreachable"
    if all(v == "intended" for v in vals):
        return "by_design"
    return "mixed"


def cmd_verify(ctx: Context, models: List[str], group: str = "function", staged: bool = True) -> Dict[str, Any]:
    audit = ctx.audit()
    review = read_json(ctx.out / "review.json")
    if review is None:
        raise UsageError("no review.json: run `review` first")
    if len(models) < 2:
        raise UsageError("verify needs two models or more")
    groups: Dict[str, Dict[str, Any]] = {}
    for f in sorted((f for f in review["findings"] if f["grade"] >= 1), key=lambda f: (f["file"], f["target"], f["run"], f["n"])):
        key = f["target"] if group == "function" else digest("file", f["file"])
        g = groups.setdefault(key, {"key": key, "target": f["target"], "file": f["file"], "function": f["function"], "claims": []})
        g["claims"].append(dict(f, k=len(g["claims"]) + 1))

    def one(job: Tuple[Dict[str, Any], str]) -> Tuple[Dict[str, Any], bool]:
        g, m = job
        rid = (digest("verify", audit["commit"], g["target"], model_id(m), *[c["id"] for c in g["claims"]]) if group == "function"
               else digest("verify", audit["commit"], "file", g["key"], model_id(m), *[c["id"] for c in g["claims"]]))
        r = ctx.stored(rid)
        if r:
            return r, False
        folder = ctx.out / "runs" / rid
        prepare_folder(ctx, folder)
        (folder / ".gitignore").write_text(".lake/\n__pycache__/\n*.pyc\n", encoding="utf-8")
        claims = []
        for c in g["claims"]:
            shutil.copy(c["repro"], folder / f"claim_{c['k']}.py")
            claims.append({"k": c["k"], "function": c["function"], "claim": c["claim"], "expected_by_the_review": c["expected"],
                           "result_now": c["result"]})
        write_json(folder / "claims.json", claims)
        head = (briefs.VERIFY_ONE_HEAD.format(n=len(claims), function=g["function"], file=g["file"]) if group == "function"
                else briefs.VERIFY_FILE_HEAD.format(n=len(claims), file=g["file"]))
        task = briefs.VERIFY.format(repo=Path(audit["repo"]).name, head=head)
        graph = agent_graph(f"hpf-{rid}", task, ["verdicts.json"], m, shell=True, check=briefs.VERIFY_CHECK, timeout=3000,
                            lean=ctx.lean)
        r = ctx.runner.run(graph, folder)
        v = read_json(folder / "verdicts.json")
        r.update(kind="verify", run=rid, folder=str(folder), target=g["target"], group=g["key"], model=model_id(m),
                 verdicts=v if isinstance(v, list) else None, finished=now())
        ctx.save(rid, r)
        return r, True

    if staged:
        # A claim is confirmed only when each verifier says `real`. So the later verifiers run only for a
        # group in which the first verifier said `real` for one claim or more.
        results = pool_map(ctx, one, [(g, models[0]) for g in groups.values()])
        first_real = {r["group"] for r, _ in results
                      if any(isinstance(v, dict) and v.get("verdict") == "real" for v in (r.get("verdicts") or []))}
        results += pool_map(ctx, one, [(g, m) for g in groups.values() if g["key"] in first_real for m in models[1:]])
    else:
        results = pool_map(ctx, one, [(g, m) for g in groups.values() for m in models])
    records = [r for r, _ in results]
    mids = [model_id(m) for m in models]
    claims_out: List[Dict[str, Any]] = []
    bugs: List[Dict[str, Any]] = []
    for g in groups.values():
        mine = {r["model"]: {v.get("k"): v for v in (r.get("verdicts") or []) if isinstance(v, dict)}
                for r in records if (r.get("group") or r["target"]) == g["key"]}
        first = mine.get(mids[0], {})
        root: Dict[int, int] = {}
        for c in g["claims"]:
            d = (first.get(c["k"]) or {}).get("duplicate_of")
            root[c["k"]] = root.get(d, d) if isinstance(d, int) and d < c["k"] and d in root else c["k"]
        rows = []
        for c in g["claims"]:
            details = {m: mine.get(m, {}).get(c["k"]) for m in mids}
            verdicts = {m: (v or {}).get("verdict") for m, v in details.items()}
            cls = verdict_class(verdicts, len(mids), staged)
            row = {"id": c["id"], "k": c["k"], "target": c["target"], "file": c["file"], "function": c["function"],
                   "claim": c["claim"], "result_now": c["result"], "repro": c["repro"], "verdicts": verdicts,
                   "class": cls, "grade": 2 if cls == "confirmed" else 1, "duplicate_of": root[c["k"]] if root[c["k"]] != c["k"] else None,
                   "details": details}
            rows.append(row)
        claims_out.extend(rows)
        clusters: Dict[int, List[Dict[str, Any]]] = {}
        for row in rows:
            if row["grade"] == 2:
                clusters.setdefault(root[row["k"]], []).append(row)
        for key, members in clusters.items():
            lead = next((x for x in rows if x["k"] == key and x["grade"] == 2), members[0])
            info = lead["details"].get(mids[0]) or {}
            bugs.append({"id": digest("bug", lead["target"], *[x["id"] for x in members]), "target": lead["target"],
                         "file": lead["file"], "function": lead["function"], "claim": lead["claim"],
                         "claims": [x["k"] for x in members], "result_now": lead["result_now"],
                         "what_goes_wrong": info.get("what_goes_wrong"), "caller": info.get("caller"),
                         "severity": info.get("severity"), "fix_idea": info.get("fix_idea"),
                         "repros": [{"finding": x["id"], "k": x["k"], "path": x["repro"], "result_now": x["result_now"]}
                                    for x in members]})
    write_json(ctx.out / "verify.json", {"models": mids, "group": group, "staged": staged, "runs": [r["run"] for r in records],
                                         "claims": claims_out})
    write_json(ctx.out / "confirmed.json", bugs)
    (ctx.out / "REPORT.md").write_text(report_md(audit, mids, claims_out, bugs), encoding="utf-8")
    failed = [{"run": r["run"], "model": r["model"], "error": r.get("error") or "no verdicts.json"}
              for r in records if r.get("error") or r.get("verdicts") is None]
    by_class: Dict[str, int] = {}
    for c in claims_out:
        by_class[c["class"]] = by_class.get(c["class"], 0) + 1
    report = {"command": "verify", "ok": not failed, "group": group, "staged": staged, "groups": len(groups), "claims": len(claims_out),
              "worker_runs": sum(1 for _, n in results if n), "reused": sum(1 for _, n in results if not n),
              "classes": by_class, "confirmed_bugs": len(bugs), "failed_runs": failed,
              "report": str(ctx.out / "REPORT.md")}
    report.update(costs(records))
    return report


def cell(x: Any) -> str:
    return str("" if x is None else x).replace("|", "\\|").replace("\n", " ")[:300]


def report_md(audit: Dict[str, Any], models: List[str], claims: List[Dict[str, Any]], bugs: List[Dict[str, Any]]) -> str:
    lines = [f"# hpflow audit of {Path(audit['repo']).name} at {audit['commit'][:12]}", "",
             f"Verifiers: {', '.join(models)}. A claim is confirmed (grade 2) when each verifier says `real`.",
             "When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.",
             "Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.", "",
             f"Confirmed bugs after duplicates fold: {len(bugs)}.", ""]
    titles = [("confirmed", "Confirmed"), ("real_unreachable", "Real but not reachable"), ("by_design", "By design"),
              ("mixed", "Mixed")]
    for cls, title in titles:
        rows = [c for c in claims if c["class"] == cls]
        lines += [f"## {title} ({len(rows)})", ""]
        if not rows:
            lines += ["None.", ""]
            continue
        lines += ["| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |",
                  "| --- | --- | --- | --- | --- | --- | --- |"]
        for c in rows:
            info = c["details"].get(models[0]) or {}
            verdicts = ", ".join(f"{m}: {v}" for m, v in c["verdicts"].items())
            lines.append(f"| `{cell(c['file'])}:{cell(c['function'])}` k={c['k']} | {cell(c['claim'])} | "
                         f"{cell(c['duplicate_of'])} | {cell(verdicts)} | `{cell(c['result_now'])}` | "
                         f"{cell(info.get('what_goes_wrong'))} | {cell(info.get('caller'))} |")
        lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------- fix

def slug_of(file: str) -> str:
    stem = file[:-3] if file.endswith(".py") else file
    return re.sub(r"[^a-z0-9]+", "-", stem.lower()).strip("-")


def bug_text(bugs: List[Dict[str, Any]]) -> str:
    rows = []
    for b in bugs:
        rows.append(f"- Bug `{b['id']}` in `{b['function']}` (claims {', '.join(str(k) for k in b['claims'])}).\n"
                    f"  What goes wrong: {b['what_goes_wrong']}\n  The review said: {b['claim']}\n"
                    f"  Result now: {b['result_now']}\n  A caller that reaches it: {b['caller']}\n"
                    f"  Fix idea of a reviewer (not binding): {b['fix_idea']}")
    return "\n".join(rows)


def fix_graph(ctx: Context, audit: Dict[str, Any], g: Dict[str, Any], base: str, info: Path, model: str,
              judge_model: str, rules: str) -> Dict[str, Any]:
    py = audit["python"]
    check = (f"PYTHONPATH={shlex.quote(str(TOOL_DIR))} {shlex.quote(sys.executable)} -m hpflow.fixcheck "
             f"{shlex.quote(str(info))}")
    test_run = audit["test_cmd"].format(python=py, tests=g["test_file"])
    fmt = dict(repo=Path(audit["repo"]).name, base=base, n=len(g["bugs"]), file=g["file"], bugs=bug_text(g["bugs"]),
               info=info, test_file=g["test_file"], test_run=test_run, rules=rules, check=check)
    tools = ["Read", "Glob", "Grep", "Write", "Edit"] + [f"Bash({c}:*)" for c in (
        "cd", "ls", "pwd", "cat", "git diff", "git status", "git log", "git show", "git grep", "git blame", "grep", "rg",
        "wc", "head", "tail", "sed", "find", "python3", py, "sort", "uniq", "diff", "echo", "test", "mkdir", "timeout")]
    payload = {"allowed_tools": tools, "disallowed_tools": ["WebFetch", "WebSearch", "Task", "Agent", "NotebookEdit"]}
    if ctx.lean:
        payload["extra_args"] = list(LEAN_ARGS)
    files = [f"{p}/**" if (ctx.src / p).is_dir() else p for p in audit["paths"]]
    if "tests/**" not in files:
        files.append("tests/**")
    return {"id": f"hpf-{digest('fixflow', g['slug'], base)}", "entry": "build",
            "defaults": {"adapter": "claude-code", "model": model_id(model), "timeout_seconds": 5400, "finish": "criteria"},
            "nodes": [
                {"id": "build", "kind": "agent", "role": "code", "files": files, "task": briefs.BUILD.format(**fmt),
                 "payload": payload},
                {"id": "check", "kind": "shell", "command": check, "timeoutMs": 2700000},
                {"id": "review", "kind": "judge", "model": model_id(judge_model), "task": briefs.JUDGE.format(**fmt),
                 "payload": payload},
                {"id": "done", "kind": "end", "status": "pass"},
                {"id": "failed", "kind": "end", "status": "fail"}],
            "edges": [{"from": "build", "to": "check", "when": "ok"},
                      {"from": "check", "to": "review", "when": "ok"},
                      {"from": "check", "to": "build", "when": "fail", "max": 2},
                      {"from": "review", "to": "done", "when": "PASS"},
                      {"from": "review", "to": "build", "when": "FAIL", "max": 2},
                      {"from": "review", "to": "build", "when": "PARTIAL", "max": 1},
                      {"from": "review", "to": "done", "when": "PARTIAL"},
                      {"from": "check", "to": "failed"}, {"from": "build", "to": "failed"},
                      {"from": "review", "to": "failed"}]}


def cmd_fix(ctx: Context, base: Optional[str], only: Optional[List[str]], model: str, judge_model: str,
            rules: Optional[str]) -> Dict[str, Any]:
    audit = ctx.audit()
    repo = Path(audit["repo"])
    bugs = read_json(ctx.out / "confirmed.json")
    if bugs is None:
        raise UsageError("no confirmed.json: run `verify` first")
    if only:
        unknown = [b for b in only if b not in {x["id"] for x in bugs}]
        if unknown:
            raise UsageError(f"no confirmed bug with the id {', '.join(unknown)}")
        bugs = [b for b in bugs if b["id"] in only]
    base_ref = base or audit["commit"]
    code, base_commit = git(repo, "rev-parse", "--verify", f"{base_ref}^{{commit}}")
    if code != 0:
        raise UsageError(f"the base {base_ref} is not a commit of {repo}")
    base_commit = base_commit.strip()
    groups: Dict[str, Dict[str, Any]] = {}
    for b in bugs:
        s = slug_of(b["file"])
        g = groups.setdefault(s, {"slug": s, "file": b["file"],
                                  "test_file": f"tests/test_hpfix_{s.replace('-', '_')}.py", "bugs": []})
        g["bugs"].append(b)

    def one(g: Dict[str, Any]) -> Tuple[Dict[str, Any], bool]:
        rid = digest("fix", audit["commit"], base_commit, g["slug"], *sorted(b["id"] for b in g["bugs"]))
        tree = ctx.out / "fix" / g["slug"]
        branch = f"hpfix/{g['slug']}"
        r = ctx.stored(rid)
        if r and tree.exists():
            return r, False
        info = ctx.out / "fixinfo" / g["slug"]
        with ctx.lock:
            if tree.exists():
                git(repo, "worktree", "remove", "--force", str(tree))
                shutil.rmtree(tree, ignore_errors=True)
            git(repo, "worktree", "prune")
            git(repo, "branch", "-D", branch)
            tree.parent.mkdir(parents=True, exist_ok=True)
            code, out = git(repo, "worktree", "add", "-q", "-b", branch, str(tree), base_commit)
        result: Dict[str, Any] = {"kind": "fix", "run": rid, "slug": g["slug"], "file": g["file"], "branch": branch,
                                  "tree": str(tree), "base": base_commit, "bugs": [b["id"] for b in g["bugs"]],
                                  "test_file": g["test_file"]}
        if code != 0:
            result.update(status="error", error="worktree", detail=out[-300:])
            ctx.save(rid, result)
            return result, True
        if info.exists():
            shutil.rmtree(info)
        info.mkdir(parents=True)
        spec_bugs = []
        for b in g["bugs"]:
            repros = []
            for rp in b["repros"]:
                name = f"{b['id']}_claim_{rp['k']}.py"
                shutil.copy(rp["path"], info / name)
                repros.append({"k": rp["k"], "file": name, "result_now": rp["result_now"]})
            spec_bugs.append({"id": b["id"], "repros": repros})
        write_json(info / "spec.json", {"file": g["file"], "test_file": g["test_file"], "python": audit["python"],
                                        "test_cmd": audit["test_cmd"], "bugs": spec_bugs})
        graph = fix_graph(ctx, audit, g, base_commit, info, model, judge_model, rules or briefs.DEFAULT_RULES)
        r = ctx.runner.run(graph, tree)
        result.update(r)
        result["check"] = fix_check(info, tree)
        _, stat = git(tree, "diff", "--stat")
        _, status = git(tree, "status", "--porcelain", "--untracked-files=all")
        result["diffstat"] = stat.strip()
        result["new_files"] = [x[3:] for x in status.splitlines() if x.startswith("??")]
        reviews = [s for s in r.get("steps") or [] if s.get("node") == "review"]
        result["judge"] = reviews[-1].get("verdict") if reviews else None
        result["finished"] = now()
        ctx.save(rid, result)
        return result, True

    results = pool_map(ctx, one, list(groups.values()))
    records = [r for r, _ in results]
    write_json(ctx.out / "fix.json", {"base": base_commit, "runs": [r["run"] for r in records]})
    rows = [{"slug": r["slug"], "worktree": r["tree"], "branch": r["branch"], "bugs": r["bugs"],
             "flow_status": r.get("status"), "diffstat": r.get("diffstat"), "new_files": r.get("new_files"),
             "check": (r.get("check") or {}).get("verdict"), "check_problems": (r.get("check") or {}).get("problems"),
             "judge": r.get("judge"), "error": r.get("error")} for r in records]
    ok = all(not r.get("error") and (r.get("check") or {}).get("verdict") == "accept" for r in records)
    report = {"command": "fix", "ok": ok, "base": base_commit, "worktrees": rows,
              "worker_runs": sum(1 for _, n in results if n), "reused": sum(1 for _, n in results if not n),
              "note": "hpflow does not commit, push or merge. Review each worktree and commit it yourself."}
    report.update(costs(records))
    return report


# ---------------------------------------------------------------- status

def accepted_fixes(fix_recs: List[Dict[str, Any]]) -> set:
    """The bugs that have a fix with an accepted script check and a PASS judge."""
    fixed: set = set()
    for r in fix_recs:
        if (r.get("check") or {}).get("verdict") == "accept" and r.get("judge") == "PASS":
            fixed.update(r.get("bugs") or [])
    return fixed


def cmd_status(ctx: Context) -> Dict[str, Any]:
    audit = ctx.audit()
    targets = (read_json(ctx.out / "targets.json") or {}).get("targets")
    review = read_json(ctx.out / "review.json")
    verify = read_json(ctx.out / "verify.json")
    confirmed = read_json(ctx.out / "confirmed.json")
    fix = read_json(ctx.out / "fix.json")

    def recs(ids: List[str]) -> List[Dict[str, Any]]:
        return [r for r in (read_json(ctx.record_path(i)) for i in ids) if r]

    steps: Dict[str, Any] = {}
    review_recs = recs((review or {}).get("runs") or [])
    verify_recs = recs((verify or {}).get("runs") or [])
    fix_recs = recs((fix or {}).get("runs") or [])
    for name, rs in (("review", review_recs), ("verify", verify_recs), ("fix", fix_recs)):
        steps[name] = dict(runs=len(rs), **costs(rs))
    grade: Dict[str, int] = {}
    if review:
        for f in review["findings"]:
            grade[f["id"]] = f["grade"]
    for c in (verify or {}).get("claims") or []:
        grade[c["id"]] = max(grade.get(c["id"], 0), c["grade"])
    fixed = accepted_fixes(fix_recs)
    for b in confirmed or []:
        if b["id"] in fixed:
            for rp in b["repros"]:
                grade[rp["finding"]] = 3
    counts = {str(n): sum(1 for v in grade.values() if v == n) for n in range(4)}
    open_items: List[str] = []
    if targets is None:
        open_items.append("targets: not run")
    if review is None:
        open_items.append("review: not run")
    else:
        done = {i for r in review_recs if not r.get("error") for i in (r.get("targets") or [r["target"]])}
        missing = [t for t in targets or [] if t["id"] not in done]
        if missing:
            open_items.append(f"review: {len(missing)} targets have no reviewer result")
        bad = [r["run"] for r in review_recs if r.get("error")]
        if bad:
            open_items.append(f"review: {len(bad)} runs failed")
    if review is not None and any(f["grade"] >= 1 for f in review["findings"]) and verify is None:
        open_items.append("verify: not run")
    if verify is not None:
        bad = [r["run"] for r in verify_recs if r.get("error") or r.get("verdicts") is None]
        if bad:
            open_items.append(f"verify: {len(bad)} runs have no verdicts")
    if confirmed:
        unfixed = [b["id"] for b in confirmed if b["id"] not in fixed]
        if unfixed:
            open_items.append(f"fix: {len(unfixed)} confirmed bugs have no accepted fix with a PASS judge")
    return {"command": "status", "ok": True, "repo": audit["repo"], "commit": audit["commit"],
            "targets": len(targets or []), "grades": counts, "confirmed_bugs": len(confirmed or []), "steps": steps,
            "not_done": open_items, "cost_note": COST_NOTE}


# ---------------------------------------------------------------- gate

def cmd_waive(ctx: Context, bug: str, reason: str, by: Optional[str]) -> Dict[str, Any]:
    """Record the decision of the owner that one confirmed bug stays as it is."""
    confirmed = read_json(ctx.out / "confirmed.json")
    if confirmed is None:
        raise UsageError("no confirmed.json: run `verify` first")
    if bug not in {b["id"] for b in confirmed}:
        raise UsageError(f"no confirmed bug with the id {bug}")
    if not reason.strip():
        raise UsageError("a waiver needs a reason")
    waivers = read_json(ctx.out / "waivers.json", {})
    waivers[bug] = {"reason": reason.strip(), "by": by, "time": now()}
    write_json(ctx.out / "waivers.json", waivers)
    return {"command": "waive", "ok": True, "bug": bug, "waivers": len(waivers)}


def cmd_gate(ctx: Context, ref: Optional[str], repro_timeout: float) -> Dict[str, Any]:
    """Pass only when the audit is complete and each confirmed bug is closed. No model call.

    With `--ref`, a bug is closed when each of its repros gives a new result on that commit.
    With no `--ref`, a bug is closed when it has a fix with an accepted check and a PASS judge.
    A waiver closes a bug in the two cases.
    """
    audit = ctx.audit()
    status = cmd_status(ctx)
    incomplete = [x for x in status["not_done"] if not x.startswith("fix:")]
    confirmed = read_json(ctx.out / "confirmed.json") or []
    waivers = read_json(ctx.out / "waivers.json", {})
    fix = read_json(ctx.out / "fix.json")
    fixed = accepted_fixes([r for r in (read_json(ctx.record_path(i)) for i in (fix or {}).get("runs") or []) if r])
    tree: Optional[Path] = None
    commit: Optional[str] = None
    if ref:
        repo = Path(audit["repo"])
        code, out = git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}")
        if code != 0:
            raise UsageError(f"the ref {ref} is not a commit of {repo}")
        commit = out.strip()
        tree = ctx.out / "gate" / commit[:12]
        if not tree.is_dir():
            tree.mkdir(parents=True)
            tarball = ctx.out / "gate.tar"
            paths = [p for p in audit["paths"] if git(repo, "cat-file", "-e", f"{commit}:{p}")[0] == 0]
            code, detail = git(repo, "archive", "-o", str(tarball), commit, *paths)
            if code == 0:
                code, detail = sh(["tar", "-x", "-f", str(tarball), "-C", str(tree)])
            tarball.unlink(missing_ok=True)
            if code != 0:
                shutil.rmtree(tree, ignore_errors=True)
                raise StepError(f"git archive failed: {detail[-300:]}")
    rows: List[Dict[str, Any]] = []
    for b in confirmed:
        row = {"id": b["id"], "file": b["file"], "function": b["function"], "what_goes_wrong": b.get("what_goes_wrong"),
               "severity": b.get("severity")}
        if b["id"] in waivers:
            row.update(state="waived", reason=waivers[b["id"]]["reason"])
        elif tree is not None:
            same, unknown = [], []
            for rp in b["repros"]:
                got = run_snippet(tree, Path(rp["path"]), ctx.home, timeout=repro_timeout)
                if got.get("ok") and got.get("result") == rp["result_now"]:
                    same.append(rp["k"])
                elif not got.get("ok") and (got.get("error") == "timeout" or got.get("error") in MISSING):
                    unknown.append(f"claim {rp['k']}: {got.get('error')}")
            if same:
                row.update(state="open", reason=f"the repro of claim {', '.join(str(k) for k in same)} gives the old result on {commit[:12]}")
            elif unknown:
                row.update(state="open", reason="the repro does not run on this commit (" + "; ".join(unknown) + "): fix the repro or record a waiver")
            else:
                row.update(state="closed", reason=f"each repro gives a new result on {commit[:12]}")
        elif b["id"] in fixed:
            row.update(state="closed", reason="a fix with an accepted check and a PASS judge is in its worktree; it is not merged by hpflow")
        else:
            row.update(state="open", reason="no accepted fix and no waiver")
        rows.append(row)
    open_rows = [r for r in rows if r["state"] == "open"]
    ok = not incomplete and not open_rows
    return {"command": "gate", "ok": ok, "verdict": "pass" if ok else "fail", "audited_commit": audit["commit"],
            "checked_commit": commit, "targets": status["targets"], "confirmed_bugs": len(confirmed),
            "closed": sum(1 for r in rows if r["state"] == "closed"), "waived": sum(1 for r in rows if r["state"] == "waived"),
            "open": open_rows, "incomplete": incomplete, "bugs": rows,
            "note": "A pass says that each bug that two verifier agents confirmed is closed or waived. It is not a proof that the code has no bug."}

