"""The commands of hpflow. Each one reads and writes JSON files in the audit folder."""
from __future__ import annotations

import ast
import posixpath
import re
import shlex
import shutil
import sys
import threading
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

from . import adapters, briefs
from .common import (COST_NOTE, DEFAULT_CONCURRENCY, MISSING, TOOL_DIR, WINDOWS, StepError, UsageError, copy_tree, digest, git, git_status,
                     is_test_file, lines_of, read_json, run_snippet, sh, shell_python, shell_quote, write_json)
from .fixcheck import check as fix_check
from .direct import check_template
from .runner import Runner, agent_graph

DEFAULT_TEST_CMD = "{python} -m pytest -q -p no:cacheprovider {tests}"
EXTRA_PATHS = ("tests", "docs", "README.md", "pyproject.toml")


class Context:
    """The audit folder, the runner and the shared options of one call."""

    def __init__(self, out: Path, runner: Runner, redo: bool = False, concurrency: int = DEFAULT_CONCURRENCY,
                 lean: bool = True, adapter: Optional[str] = None, agent_cmd: Optional[str] = None,
                 effort: str = adapters.DEFAULT_EFFORT):
        self.lean = lean
        self.given_adapter = adapter
        self.given_agent_cmd = agent_cmd
        self.effort = effort
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

    def adapter(self) -> str:
        """The adapter of the workers of this call.

        The rule: an `--adapter` option wins and becomes the adapter of the audit folder (the key `adapter` of
        audit.json). With no option, a command uses the adapter of the audit folder, else `claude-code`. So a later
        `verify`, `fix` or `status` uses the adapter of the last command that named one."""
        return self.given_adapter or self.audit().get("adapter") or adapters.DEFAULT_ADAPTER

    def agent_cmd(self) -> Optional[str]:
        """The command template of `--adapter command`, with the same rule as the adapter (the key `agent_cmd`)."""
        return self.given_agent_cmd or self.audit().get("agent_cmd")

    def check_adapter(self) -> Tuple[str, Optional[str]]:
        """The adapter and the command template of this call. A usage error when they cannot start a worker."""
        adapter, template = self.adapter(), self.agent_cmd()
        adapters.check(adapter, template)
        if adapter == adapters.COMMAND:
            check_template(str(template))
        return adapter, template if adapter == adapters.COMMAND else None

    def keep_adapter(self) -> None:
        """Store `--adapter` and `--agent-cmd` in audit.json. A command calls it after its options are valid."""
        audit = self.audit()
        new = dict(audit)
        if self.given_adapter:
            new["adapter"] = self.given_adapter
        if self.given_agent_cmd:
            new["agent_cmd"] = self.given_agent_cmd
        if new != audit:
            write_json(self.out / "audit.json", new)

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


def adapter_key(adapter: str, agent_cmd: Optional[str] = None, effort: str = adapters.DEFAULT_EFFORT) -> List[str]:
    """The worker part of a record id: the adapter, the command template and the effort.

    The default adapter and the default effort add nothing, so the ids of hpflow 0.4 stay valid (its workers
    ran on Claude Code, and Puppetmaster gave them `--effort medium`)."""
    key = [] if adapter == adapters.DEFAULT_ADAPTER else [adapter]
    if agent_cmd:
        key.append(agent_cmd)
    # The command adapter does not pass the effort to its tool, so the effort does not change its result.
    if effort != adapters.DEFAULT_EFFORT and adapter != adapters.COMMAND:
        key.append(f"effort={effort}")
    return key


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def pool_map(ctx: Context, fn: Callable[[Any], Any], items: List[Any]) -> List[Any]:
    if not items:
        return []
    with ThreadPoolExecutor(max_workers=ctx.concurrency) as pool:
        return list(pool.map(fn, items))


def costs(records: List[Dict[str, Any]]) -> Dict[str, Any]:
    """The cost and the time of worker records. One run with an unknown cost makes the total unknown (None)."""
    known = round(sum(r.get("cost_usd") or 0 for r in records), 4)
    unknown = sum(1 for r in records if "cost_usd" in r and r["cost_usd"] is None)
    out: Dict[str, Any] = {"cost_usd_api_equivalent": None if unknown else known,
                           "seconds": round(sum(r.get("seconds") or 0 for r in records)), "cost_note": COST_NOTE}
    if unknown:
        out.update(cost_unknown_runs=unknown, cost_usd_of_the_other_runs=known)
    return out


def adapter_report(ctx: Context, adapter: str) -> Dict[str, Any]:
    out = {"adapter": adapter, "adapter_notes": adapters.notes(adapter, ctx.lean)}
    if adapter != adapters.COMMAND:
        out["effort"] = ctx.effort
    return out


# ---------------------------------------------------------------- init

def repo_path(text: str, option: str) -> str:
    """One form for a path of the repository: forward slashes, no `./`, no `..`, no slash at the end. "" is the root.

    git gives each name in this form, so a path of the user in another form (`./pkg`, `pkg/`, `a/../pkg`) would
    match no file."""
    norm = posixpath.normpath(text.replace("\\", "/"))
    if norm.startswith("/") or norm == ".." or norm.startswith("../") or re.match(r"^[A-Za-z]:", norm):
        raise UsageError(f"{option} takes a path inside the repository, not {text}")
    return "" if norm == "." else norm


def cmd_init(ctx: Context, repo: str, ref: str, paths: Optional[List[str]], python: Optional[str],
             test_cmd: Optional[str], import_root: Optional[str] = None) -> Dict[str, Any]:
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

    import_root = repo_path(import_root or ".", "--import-root")
    if import_root and not present(import_root):
        raise UsageError(f"the import root {import_root} is not in {commit[:12]}")
    if paths:
        paths = [repo_path(p, "--paths") for p in paths]
        if "" in paths:
            raise UsageError("--paths takes folders and files of the repository, not the repository root")
        missing = [p for p in paths if not present(p)]
        if missing:
            raise UsageError(f"these paths are not in {commit[:12]}: {', '.join(missing)}")
    else:
        base = f"{import_root}/" if import_root else ""
        # With -z git does not quote a name with non-ASCII characters, and a name can hold a space.
        _, listing = git(root, "ls-tree", "-z", "--name-only", "-d", f"{commit}:{import_root}" if import_root else commit)
        paths = [base + d for d in listing.split("\0") if d and d not in EXTRA_PATHS and present(f"{base}{d}/__init__.py")]
        # Check before the extra paths: they hold no package, so an audit of only them reviews no code.
        if not paths:
            raise UsageError("no package folder (a folder with __init__.py at the top level or below --import-root) "
                             "found: give --paths, and --import-root for a layout such as src/")
        paths += [p for p in EXTRA_PATHS if present(p)]
    if python is None:
        venv = root / ".venv" / "bin" / "python"
        python = str(venv) if venv.exists() else sys.executable
    old = read_json(ctx.out / "audit.json")
    if old and old.get("commit") != commit and not ctx.redo:
        raise UsageError(f"{ctx.out} holds an audit of {old.get('commit', '')[:12]}: use a new --out or --redo")
    audit = {"repo": str(root), "ref": ref, "commit": commit, "paths": paths, "python": python,
             "test_cmd": test_cmd or DEFAULT_TEST_CMD, "created": (old or {}).get("created") or now()}
    if import_root:
        audit["import_root"] = import_root
    for key in ("adapter", "agent_cmd"):
        if (old or {}).get(key):
            audit[key] = old[key]
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
    """The functions and methods of a module: qualified name, first line (decorators included), last line.

    Two definitions can have one qualified name (a property getter and its setter, or a function that a later
    `def` replaces). `nth` is the number of the definition among those with its name, in source order, and `of`
    is how many there are. The name and `nth` together are the identity of a function in its file."""
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
    count: Dict[str, int] = {}
    for fn in out:
        count[fn["function"]] = count.get(fn["function"], 0) + 1
        fn["nth"] = count[fn["function"]]
    for fn in out:
        fn["of"] = count[fn["function"]]
    return out


HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def hunk_ranges(diff: str) -> Dict[str, List[Tuple[int, int]]]:
    """The line ranges of the hunks of a `git diff -U0` of one file: `old_ranges` are the lines that the change
    removed from the old file, and `new_ranges` are the lines that it added to the new file.

    Only a hunk header starts with "@@ ": each content line of a diff starts with "+", "-" or a backslash. The
    file headers are not read here, so the text of a changed line cannot be taken for one. A hunk that only adds
    lines has no old range, and a hunk that only removes lines has no new range."""
    out: Dict[str, List[Tuple[int, int]]] = {"old_ranges": [], "new_ranges": []}
    for line in lines_of(diff):
        m = HUNK.match(line)
        if not m:
            continue
        old_start, old_count = int(m.group(1)), 1 if m.group(2) is None else int(m.group(2))
        new_start, new_count = int(m.group(3)), 1 if m.group(4) is None else int(m.group(4))
        if old_count:
            out["old_ranges"].append((old_start, old_start + old_count - 1))
        if new_count:
            out["new_ranges"].append((new_start, new_start + new_count - 1))
    return out


def changed_files(repo: Path, a: str, b: str, paths: List[str]) -> List[Dict[str, Any]]:
    """Each file that differs between two commits: its old and new path and the line ranges of its hunks.

    The names come from `git diff --name-status -z`: a list with NUL between the fields, which git does not
    quote. So a name with a space, a tab, a quote or a non-ASCII character is the real name. The diff of one
    file gets its name as a literal path (see `common.git`), so a name such as `a[b].py` selects only that file."""
    code, out = git(repo, "diff", "--name-status", "-z", "--no-ext-diff", "-M", a, b, "--", *paths)
    if code != 0:
        raise StepError(f"git diff failed: {out[-300:]}")
    fields = out.split("\0")
    files: List[Dict[str, Any]] = []
    i = 0
    while i < len(fields) and fields[i]:
        status = fields[i]
        if status[0] in "RC":
            old, new = fields[i + 1], fields[i + 2]
            i += 3
        else:
            old = None if status[0] == "A" else fields[i + 1]
            new = None if status[0] == "D" else fields[i + 1]
            i += 2
        code, diff = git(repo, "diff", "-U0", "--no-color", "--no-ext-diff", "-M", a, b, "--", *[p for p in (old, new) if p])
        if code != 0:
            raise StepError(f"git diff failed: {diff[-300:]}")
        files.append(dict({"old": old, "new": new}, **hunk_ranges(diff)))
    return files


def overlaps(fn: Dict[str, Any], ranges: List[Tuple[int, int]]) -> bool:
    return any(a <= fn["end"] and fn["start"] <= b for a, b in ranges)


def top_of(file: str, import_root: str = "") -> str:
    """The top-level module of a file: its first folder below the import root."""
    if import_root and file.startswith(import_root + "/"):
        file = file[len(import_root) + 1:]
    parts = Path(file).parts
    return parts[0] if len(parts) > 1 else Path(file).stem


def make_target(file: str, fn: Dict[str, Any], how: str, import_root: str = "") -> Dict[str, Any]:
    """The target of one function. `fn` is a record of `functions_of`.

    The id comes from the identity of the function: the file, the qualified name and `nth`. The first definition
    of a name has the id that hpflow 0.4 gave it, so an audit folder of 0.4 keeps its stored runs. A later
    definition of the same name has its number in the id, so it is a target of its own."""
    nth = fn["nth"]
    identity = (file, fn["function"]) if nth == 1 else (file, fn["function"], nth)
    return {"id": digest("target", *identity), "file": file, "function": fn["function"], "nth": nth, "of": fn["of"],
            "top": top_of(file, import_root),
            "lines": [fn["start"], fn["end"]], "length": fn["end"] - fn["start"] + 1, "source": how}


def target_label(t: Dict[str, Any]) -> str:
    """The name of a target for a worker. A name with more than one definition in its file gets the line of this one."""
    if (t.get("of") or 1) == 1:
        return t["function"]
    return f"{t['function']} (definition {t['nth']} of {t['of']} with this name, at line {t['lines'][0]})"


def in_paths(file: str, paths: List[str]) -> bool:
    return any(file == p or file.startswith(p.rstrip("/") + "/") for p in paths)


def cmd_targets(ctx: Context, changed: Optional[str], functions: Optional[List[str]], files: Optional[List[str]],
                max_lines: int, max_n: Optional[int]) -> Dict[str, Any]:
    audit = ctx.audit()
    import_root = audit.get("import_root") or ""
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
        for f in changed_files(repo, a, b, audit["paths"]):
            path = f["new"] or f["old"]
            if not path or not path.endswith(".py") or not in_paths(path, audit["paths"]):
                continue
            new_fns = functions_of(git(repo, "show", f"{b}:{f['new']}")[1]) if f["new"] else []
            old_fns = functions_of(git(repo, "show", f"{a}:{f['old']}")[1]) if f["old"] else []
            # A function is its qualified name and `nth`. The change touched a function of the new file when a
            # hunk added a line to it, or when a hunk removed a line from the definition that it had before.
            before = {(fn["function"], fn["nth"]): fn for fn in old_fns}
            after = {(fn["function"], fn["nth"]) for fn in new_fns}

            def touched(fn: Dict[str, Any]) -> bool:
                was = before.get((fn["function"], fn["nth"]))
                return overlaps(fn, f["new_ranges"]) or (was is not None and overlaps(was, f["old_ranges"]))

            if is_test_file(path):
                hit = [fn for fn in new_fns if touched(fn)]
                for fn in hit:
                    skipped.append({"file": path, "function": fn["function"], "reason": "test file"})
                if not hit:
                    skipped.append({"file": path, "function": None, "reason": "test file"})
                continue
            for fn in old_fns:
                # A definition that the new file does not have. No diff can drop it and leave its lines.
                if (fn["function"], fn["nth"]) not in after:
                    skipped.append({"file": path, "function": fn["function"], "reason": "removed"})
            for fn in new_fns:
                if touched(fn):
                    candidates.append(make_target(f["new"], fn, "changed", import_root))
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
                candidates.append(make_target(file, fn, "function" if name else "file", import_root))
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


def cmd_review(ctx: Context, model: Optional[str], shell: bool, passes: int, repro_timeout: float, group: str = "function",
               group_size: int = 6, short_prompt: bool = False) -> Dict[str, Any]:
    audit = ctx.audit()
    import_root = audit.get("import_root") or ""
    # The folder of a worker that is first on the import path of a repro.
    root = "project/" + (f"{import_root}/" if import_root else "")
    targets = (read_json(ctx.out / "targets.json") or {}).get("targets")
    if targets is None:
        raise UsageError("no targets.json: run `targets` first")
    adapter, template = ctx.check_adapter()
    mid = adapters.model_id(adapter, adapters.model_or_default(adapter, model, "sonnet", "--model"))
    payload = adapters.payload(adapter, shell=shell, lean=ctx.lean, effort=ctx.effort, agent_cmd=template, reviewer=short_prompt)
    key = adapter_key(adapter, template, ctx.effort)
    if short_prompt:
        # The short prompt changes the system prompt and the brief, so its records are not those of the default prompt.
        key.append("short_prompt")
    ctx.keep_adapter()
    arm = "shell" if shell else "plain"
    arm_text = briefs.REVIEW_ARM[arm] + (adapters.review_hint(adapter) if ctx.lean and short_prompt else "")
    jobs = [(ts, p) for ts in review_groups(targets, group, group_size) for p in range(1, passes + 1)]

    def one(job: Tuple[List[Dict[str, Any]], int]) -> Tuple[Dict[str, Any], bool]:
        ts, p = job
        t = ts[0]
        single = group == "function"
        rid = (digest("review", audit["commit"], t["id"], p, *key, mid, arm) if single
               else digest("review", audit["commit"], "file", *[x["id"] for x in ts], p, *key, mid, arm))
        r = ctx.stored(rid)
        if r:
            return r, False
        folder = ctx.out / "runs" / rid
        prepare_folder(ctx, folder)
        if single:
            task = briefs.REVIEW.format(function=target_label(t), file=t["file"], top=t["top"], arm_text=arm_text, root=root)
            check = shell_python(briefs.REVIEW_CHECK)
        else:
            write_json(folder / "functions.json", [target_label(x) for x in ts])
            task = briefs.REVIEW_FILE.format(functions="\n".join(f"- `{target_label(x)}`" for x in ts), file=t["file"], top=t["top"], root=root,
                                             per_function=briefs.PER_FUNCTION, arm_text=arm_text)
            check = shell_python(briefs.REVIEW_FILE_CHECK)
        graph = agent_graph(f"hpf-{rid}", task, ["findings.json", "finding_*.py"], adapter, mid, payload, check=check,
                            timeout=2400)
        r = ctx.runner.run(graph, folder)
        r.update(kind="review", run=rid, folder=str(folder), target=t["id"], targets=[x["id"] for x in ts], pass_n=p,
                 adapter=adapter, model=mid, arm=arm, finished=now())
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
            # Store the note: `status` and `gate` read the record, and a run with no report is not a review.
            r["note"] = "no valid findings.json"
            ctx.save(r["run"], r)
            return []
        out = []
        mine = [by_id[i] for i in (r.get("targets") or [r["target"]])]
        by_name = {target_label(t): t for t in mine}
        seen: Dict[str, int] = {}
        # The group decides the brief, so it decides the rules: a file chunk can hold one function.
        single = group == "function"
        for i, f in enumerate(items[:5] if single else items):
            if not isinstance(f, dict):
                continue
            n = f.get("n", i + 1)
            t = mine[0] if single else by_name.get(str(f.get("function")))
            if t is None:
                r["note_unknown_function"] = f"finding {n} names a function that is not in the list"
                continue
            seen[t["id"]] = seen.get(t["id"], 0) + 1
            if not single and seen[t["id"]] > briefs.PER_FUNCTION:
                continue
            row = {"id": f"{r['run']}-{n}", "run": r["run"], "n": n, "target": t["id"], "file": t["file"],
                   "function": t["function"], "model": r["model"], "claim": str(f.get("claim"))[:600],
                   "expected": str(f.get("expected"))[:300], "confidence": f.get("confidence"),
                   "repro": str(folder / f"finding_{n}.py")}
            snippet = folder / f"finding_{n}.py"
            if not snippet.exists():
                row.update(grade=0, reason="no repro file")
            else:
                got = run_snippet(ctx.src, snippet, ctx.home, timeout=repro_timeout, import_root=import_root)
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
    write_json(ctx.out / "review.json", {"adapter": adapter, "model": mid, "arm": arm, "passes": passes, "group": group,
                                         "runs": [r["run"] for r in records], "findings": findings})
    failed = [{"run": r["run"], "target": r["target"], "error": r.get("error") or r.get("note") or r.get("status")}
              for r in records if r.get("error") or r.get("note")]
    report = {"command": "review", "ok": not failed, "runs": len(records), "worker_runs": sum(1 for _, n in results if n),
              "reused": sum(1 for _, n in results if not n), "group": group, "findings": len(findings),
              "grade_1": sum(1 for f in findings if f["grade"] == 1),
              "grade_0": [{"id": f["id"], "reason": f["reason"]} for f in findings if f["grade"] == 0],
              "failed_runs": failed}
    report.update(adapter_report(ctx, adapter))
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


def cmd_verify(ctx: Context, models: Optional[List[str]], group: str = "function", staged: bool = True) -> Dict[str, Any]:
    audit = ctx.audit()
    review = read_json(ctx.out / "review.json")
    if review is None:
        raise UsageError("no review.json: run `review` first")
    adapter, template = ctx.check_adapter()
    mids = [adapters.model_id(adapter, m) for m in adapters.model_or_default(adapter, models, ["sonnet", "opus"], "--models")]
    if len(mids) < 2:
        raise UsageError("verify needs two models or more")
    if len(set(mids)) < len(mids):
        raise UsageError("give each verifier model once: the verdicts of one model are stored under its id")
    payload = adapters.payload(adapter, shell=True, lean=ctx.lean, effort=ctx.effort, agent_cmd=template)
    key = adapter_key(adapter, template, ctx.effort)
    ctx.keep_adapter()
    groups: Dict[str, Dict[str, Any]] = {}
    for f in sorted((f for f in review["findings"] if f["grade"] >= 1), key=lambda f: (f["file"], f["target"], f["run"], f["n"])):
        gkey = f["target"] if group == "function" else digest("file", f["file"])
        g = groups.setdefault(gkey, {"key": gkey, "target": f["target"], "file": f["file"], "function": f["function"], "claims": []})
        g["claims"].append(dict(f, k=len(g["claims"]) + 1))

    def one(job: Tuple[Dict[str, Any], str]) -> Tuple[Dict[str, Any], bool]:
        g, m = job
        rid = (digest("verify", audit["commit"], g["target"], *key, m, *[c["id"] for c in g["claims"]]) if group == "function"
               else digest("verify", audit["commit"], "file", g["key"], *key, m, *[c["id"] for c in g["claims"]]))
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
        task = briefs.VERIFY.format(repo=Path(audit["repo"]).name, head=head, imp=audit.get("import_root") or ".")
        graph = agent_graph(f"hpf-{rid}", task, ["verdicts.json"], adapter, m, payload, check=shell_python(briefs.VERIFY_CHECK), timeout=3000)
        r = ctx.runner.run(graph, folder)
        v = read_json(folder / "verdicts.json")
        r.update(kind="verify", run=rid, folder=str(folder), target=g["target"], group=g["key"], adapter=adapter, model=m,
                 verdicts=v if isinstance(v, list) else None, finished=now())
        ctx.save(rid, r)
        return r, True

    if staged:
        # A claim is confirmed only when each verifier says `real`. So the later verifiers run only for a
        # group in which the first verifier said `real` for one claim or more.
        results = pool_map(ctx, one, [(g, mids[0]) for g in groups.values()])
        first_real = {r["group"] for r, _ in results
                      if any(isinstance(v, dict) and v.get("verdict") == "real" for v in (r.get("verdicts") or []))}
        results += pool_map(ctx, one, [(g, m) for g in groups.values() if g["key"] in first_real for m in mids[1:]])
    else:
        results = pool_map(ctx, one, [(g, m) for g in groups.values() for m in mids])
    records = [r for r, _ in results]
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
    write_json(ctx.out / "verify.json", {"adapter": adapter, "models": mids, "group": group, "staged": staged,
                                         "runs": [r["run"] for r in records],
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
    report.update(adapter_report(ctx, adapter))
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

def slug_of(file: str, unique: bool = False) -> str:
    """The name of the worktree, branch and test file of a file. With `unique`, a part of the digest of the path
    keeps apart the files whose plain slugs are the same (pkg/a_b.py and pkg/a/b.py give pkg-a-b)."""
    stem = file[:-3] if file.endswith(".py") else file
    slug = re.sub(r"[^a-z0-9]+", "-", stem.lower()).strip("-")
    # A path that is not a module path (pkg/a-b.py) cannot be imported, and its slug would take the name of one.
    if unique or not re.fullmatch(r"[A-Za-z0-9_]+(/[A-Za-z0-9_]+)*\.py", file):
        return f"{slug}-{digest('slug', file)[-8:]}"
    return slug


def bug_text(bugs: List[Dict[str, Any]]) -> str:
    rows = []
    for b in bugs:
        rows.append(f"- Bug `{b['id']}` in `{b['function']}` (claims {', '.join(str(k) for k in b['claims'])}).\n"
                    f"  What goes wrong: {b['what_goes_wrong']}\n  The review said: {b['claim']}\n"
                    f"  Result now: {b['result_now']}\n  A caller that reaches it: {b['caller']}\n"
                    f"  Fix idea of a reviewer (not binding): {b['fix_idea']}")
    return "\n".join(rows)


def check_script(info: Path) -> str:
    """The text of `check.py` in the info folder of a fix: it runs `hpflow.fixcheck` on that folder.

    A file, not a `PYTHONPATH=... python -m` line: the worker and the judge can then run the check with one plain
    command that their allow list has, and the same command works in cmd.exe."""
    return ("import runpy\nimport sys\n\n"
            f"sys.path.insert(0, {str(TOOL_DIR)!r})\n"
            f"sys.argv = ['hpflow.fixcheck', {str(info)!r}]\n"
            "runpy.run_module('hpflow.fixcheck', run_name='__main__')\n")


def fixcheck_command(info: Path) -> str:
    """The shell command of the script check of a fix."""
    utf8 = " -X utf8" if WINDOWS else ""
    return f"{shell_quote(sys.executable)}{utf8} {shell_quote(str(info / 'check.py'))}"


def fix_key(adapter: str, model: str, judge_model: str, rules: str) -> List[str]:
    """The part of a fix id for the models and the rules. The defaults add nothing, so the ids of hpflow 0.4 stay
    valid: its fix workers ran on Opus with a Sonnet judge and the default rules."""
    default = (adapter == adapters.DEFAULT_ADAPTER and model == adapters.CLAUDE_MODELS["opus"]
               and judge_model == adapters.CLAUDE_MODELS["sonnet"] and rules == briefs.DEFAULT_RULES)
    return [] if default else [model, judge_model, digest("rules", rules)]


def fix_scope(ctx: Context, audit: Dict[str, Any]) -> List[str]:
    """The paths that a fix worker can change: the audit paths and the tests."""
    files = [f"{p}/**" if (ctx.src / p).is_dir() else p for p in audit["paths"]]
    if "tests/**" not in files:
        files.append("tests/**")
    return files


def fix_graph(ctx: Context, audit: Dict[str, Any], g: Dict[str, Any], base: str, info: Path, adapter: str,
              template: Optional[str], model: str, judge_model: str, rules: str) -> Dict[str, Any]:
    py = audit["python"]
    check = fixcheck_command(info)
    # Quoted as fixcheck.test_command does, so a python path with a space stays one argument.
    test_run = audit["test_cmd"].format(python=shell_quote(py), tests=shell_quote(g["test_file"]))
    fmt = dict(repo=Path(audit["repo"]).name, base=base, n=len(g["bugs"]), file=g["file"], bugs=bug_text(g["bugs"]),
               info=info, test_file=g["test_file"], test_run=test_run, rules=rules, check=check)
    # The check command is in the list, so the worker and the judge can run it as the brief says.
    commands = (*adapters.FIX_COMMANDS, py, check)
    payload = adapters.payload(adapter, shell=True, lean=ctx.lean, commands=commands, effort=ctx.effort, agent_cmd=template)
    judge_payload = adapters.payload(adapter, judge=True, shell=True, lean=ctx.lean, commands=commands, effort=ctx.effort,
                                     agent_cmd=template)
    files = fix_scope(ctx, audit)
    # The bugs are a part of the id: two runs for one file with other bugs (`--only`) must not share a graph file.
    fid = digest("fixflow", g["slug"], base, *adapter_key(adapter, template, ctx.effort),
                 *fix_key(adapter, model, judge_model, rules), *sorted(b["id"] for b in g["bugs"]))
    return {"id": f"hpf-{fid}", "entry": "build",
            "defaults": {"adapter": adapter, "model": model, "timeout_seconds": 5400, "finish": "criteria"},
            "nodes": [
                {"id": "build", "kind": "agent", "role": "code", "files": files, "task": briefs.BUILD.format(**fmt),
                 "payload": payload},
                {"id": "check", "kind": "shell", "command": check, "timeoutMs": 2700000},
                {"id": "review", "kind": "judge", "model": judge_model, "task": briefs.JUDGE.format(**fmt),
                 "payload": judge_payload},
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


def cmd_fix(ctx: Context, base: Optional[str], only: Optional[List[str]], model: Optional[str], judge_model: Optional[str],
            rules: Optional[str]) -> Dict[str, Any]:
    audit = ctx.audit()
    adapter, template = ctx.check_adapter()
    model = adapters.model_id(adapter, adapters.model_or_default(adapter, model, "opus", "--model"))
    judge_model = adapters.model_id(adapter, adapters.model_or_default(adapter, judge_model, "sonnet", "--judge-model"))
    ctx.keep_adapter()
    rules_text = rules or briefs.DEFAULT_RULES
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
    # The new test file goes into the tests folder of the audit paths (for example `tool/tests`), else `tests`.
    tests_dir = next((p for p in audit["paths"] if Path(p).name == "tests"), "tests")
    plain: Dict[str, set] = {}
    for b in bugs:
        plain.setdefault(slug_of(b["file"]), set()).add(b["file"])
    for b in bugs:
        s = slug_of(b["file"], unique=len(plain[slug_of(b["file"])]) > 1)
        g = groups.setdefault(b["file"], {"slug": s, "file": b["file"],
                                          "test_file": f"{tests_dir}/test_hpfix_{s.replace('-', '_')}.py", "bugs": []})
        g["bugs"].append(b)

    def one(g: Dict[str, Any]) -> Tuple[Dict[str, Any], bool]:
        # The models and the rules change the fix, so a run with others does not reuse the stored one.
        rid = digest("fix", audit["commit"], base_commit, g["slug"], *adapter_key(adapter, template, ctx.effort),
                     *sorted(b["id"] for b in g["bugs"]), *fix_key(adapter, model, judge_model, rules_text))
        tree = ctx.out / "fix" / g["slug"]
        # The audit folder and the id of the run are a part of the branch name. A second audit of the same
        # repository then has branches of its own, and this run never deletes the branch of another audit.
        branch = f"hpfix/{g['slug']}-{digest('branch', str(ctx.out), rid)[:8]}"
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
        result: Dict[str, Any] = {"kind": "fix", "run": rid, "adapter": adapter, "model": model, "judge_model": judge_model,
                                  "slug": g["slug"], "file": g["file"], "branch": branch,
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
                                        "test_cmd": audit["test_cmd"], "bugs": spec_bugs, "scope": fix_scope(ctx, audit),
                                        "import_root": audit.get("import_root") or "", "tests_dir": tests_dir})
        (info / "check.py").write_text(check_script(info), encoding="utf-8")
        graph = fix_graph(ctx, audit, g, base_commit, info, adapter, template, model, judge_model, rules_text)
        r = ctx.runner.run(graph, tree)
        result.update(r)
        result["check"] = fix_check(info, tree)
        _, stat = git(tree, "diff", "--stat")
        result["diffstat"] = stat.strip()
        result["new_files"] = [e["path"] for e in git_status(tree) or [] if e["status"] == "??"]
        reviews = [s for s in r.get("steps") or [] if s.get("node") == "review"]
        result["judge"] = reviews[-1].get("verdict") if reviews else None
        result["finished"] = now()
        ctx.save(rid, result)
        return result, True

    results = pool_map(ctx, one, list(groups.values()))
    records = [r for r, _ in results]
    write_json(ctx.out / "fix.json", {"adapter": adapter, "base": base_commit, "runs": [r["run"] for r in records]})
    rows = [{"slug": r["slug"], "worktree": r["tree"], "branch": r["branch"], "bugs": r["bugs"],
             "flow_status": r.get("status"), "diffstat": r.get("diffstat"), "new_files": r.get("new_files"),
             "check": (r.get("check") or {}).get("verdict"), "check_problems": (r.get("check") or {}).get("problems"),
             "judge": r.get("judge"), "error": r.get("error")} for r in records]
    ok = all(not r.get("error") and (r.get("check") or {}).get("verdict") == "accept" for r in records)
    report = {"command": "fix", "ok": ok, "base": base_commit, "worktrees": rows,
              "worker_runs": sum(1 for _, n in results if n), "reused": sum(1 for _, n in results if not n),
              "note": "hpflow does not commit, push or merge. Review each worktree and commit it yourself."}
    report.update(adapter_report(ctx, adapter))
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
        # A record of hpflow 0.4 has no `adapter` key: those workers ran on Claude Code.
        steps[name] = dict(runs=len(rs), adapters=sorted({r.get("adapter") or adapters.DEFAULT_ADAPTER for r in rs}), **costs(rs))
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
        # A run with an error (the worker did not start) or a note (it wrote no valid report) reviewed nothing.
        done = {i for r in review_recs if not (r.get("error") or r.get("note")) for i in (r.get("targets") or [r["target"]])}
        missing = [t for t in targets or [] if t["id"] not in done]
        if missing:
            open_items.append(f"review: {len(missing)} targets have no reviewer result")
        bad = [r["run"] for r in review_recs if r.get("error") or r.get("note")]
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
            "adapter": audit.get("adapter") or adapters.DEFAULT_ADAPTER,
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
                got = run_snippet(tree, Path(rp["path"]), ctx.home, timeout=repro_timeout, import_root=audit.get("import_root") or "")
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

