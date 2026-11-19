"""Shared parts of hpflow: files, hashes, shell calls, the repro runner and the cost rule."""
from __future__ import annotations

import hashlib
import json
import os
import shlex
import shutil
import signal
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

DEFAULT_CONCURRENCY = 5
COST_NOTE = ("Cost is API-equivalent, as the provider tool reports it. "
             "Plan billing can apply, so the real charge can be lower. "
             "A cost of null is unknown: hpflow reads `total_cost_usd`, and only the Claude Code CLI reports it.")
TOOL_DIR = Path(__file__).resolve().parent.parent


WINDOWS = os.name == "nt"


def shell_quote(text: str) -> str:
    """One argument of a shell command line: for `sh` on POSIX, for cmd.exe on Windows (cmd.exe does not read
    single quotes)."""
    return subprocess.list2cmdline([text]) if WINDOWS else shlex.quote(text)


def shell_python(command: str) -> str:
    """A check command of a brief for this system. The briefs start a check with `python3`. A Windows machine
    often has no `python3`, so there the check starts with the Python of hpflow, in UTF-8 mode: the default text
    encoding of Windows cannot read every file that an agent writes. On POSIX the command stays as it is."""
    if WINDOWS and command.startswith("python3 "):
        return shell_quote(sys.executable) + " -X utf8" + command[len("python3"):]
    return command


def snippet_env(home: Path) -> Dict[str, str]:
    """The small environment of a repro. A Python child on Windows needs SYSTEMROOT, and finds the home in
    USERPROFILE."""
    env = {"HOME": str(home), "PYTHONDONTWRITEBYTECODE": "1"}
    if WINDOWS:
        root = os.environ.get("SYSTEMROOT", r"C:\Windows")
        env.update(SYSTEMROOT=root, PATH=os.pathsep.join([os.path.join(root, "System32"), root]),
                   USERPROFILE=str(home), PYTHONUTF8="1")
    else:
        env["PATH"] = "/usr/bin:/bin"
    return env


class UsageError(Exception):
    """A bad argument or a missing input. Exit code 2."""


class StepError(Exception):
    """A step that failed. Exit code 1."""


def digest(*parts: Any) -> str:
    """A name made of digits only. A digit name cannot hold a word or the name of a function."""
    h = hashlib.sha256("|".join(str(p) for p in parts).encode()).hexdigest()
    return str(int(h[:16], 16)).zfill(20)


def read_json(path: Path, default: Any = None) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return default


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
    tmp.replace(path)


def kill_group(p: subprocess.Popen) -> None:
    """End the whole process group of `p`. A child that a command starts must not live on after a timeout."""
    if WINDOWS:
        # Windows has no process group signal. `taskkill /T` ends the process and each child that it started.
        # It cannot find the children of a leader that is gone, so a child that outlives its leader stays.
        try:
            subprocess.run(["taskkill", "/T", "/F", "/PID", str(p.pid)], capture_output=True, timeout=30)
        except (OSError, subprocess.TimeoutExpired):
            pass
        if p.poll() is None:
            p.kill()
        return
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def run_group(cmd: Union[str, List[str]], cwd: Optional[Path] = None, timeout: float = 600, shell: bool = False,
              env: Optional[Dict[str, str]] = None, stdin: Optional[str] = None) -> Tuple[Optional[int], str, str]:
    """Run a command in its own process group. At the timeout the whole group ends.

    `stdin` is the text on the standard input; with None the input is empty.
    Returns (exit code, stdout, stderr). The exit code is None after a timeout.
    """
    try:
        group: Dict[str, Any] = ({"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP} if WINDOWS  # type: ignore[attr-defined]
                                 else {"start_new_session": True})
        # Bytes, not text mode: Windows text mode writes `\n` as `\r\n`, so a tool would read on its standard input
        # another text than the prompt file. The output is UTF-8 on each system, with the newlines of text mode.
        p = subprocess.Popen(cmd, cwd=str(cwd) if cwd else None, shell=shell, env=env,
                             stdin=subprocess.DEVNULL if stdin is None else subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, **group)
    except OSError as e:
        return 127, "", str(e)
    data = None if stdin is None else stdin.encode("utf-8")
    try:
        out, err = p.communicate(input=data, timeout=timeout)
    except subprocess.TimeoutExpired:
        kill_group(p)
        out, err = p.communicate()
        return None, decode(out), decode(err)
    except BaseException:
        kill_group(p)
        p.wait()
        raise
    # The leader can exit while a child of its group still runs. That child must end too.
    kill_group(p)
    return p.returncode, decode(out), decode(err)


def decode(data: Optional[bytes]) -> str:
    """Output as text mode reads it: UTF-8 with replacement, and each `\r\n` or `\r` as `\n`."""
    return (data or b"").decode("utf-8", "replace").replace("\r\n", "\n").replace("\r", "\n")


def sh(cmd: List[str], cwd: Optional[Path] = None, timeout: float = 600) -> Tuple[int, str]:
    code, out, err = run_group(cmd, cwd, timeout)
    if code is None:
        return 124, "timeout"
    return code, out + err


def git(repo: Path, *args: str, timeout: float = 600) -> Tuple[int, str]:
    code, out, err = run_group(["git", "-C", str(repo), *args], timeout=timeout)
    if code is None:
        return 124, "timeout"
    return code, out if code == 0 else out + err


def copy_tree(src: Path, dest: Path) -> None:
    """Copy a folder. On macOS `cp -Rc` makes a clone, which is fast and uses no space."""
    if sys.platform == "darwin" and not dest.exists():
        code, _ = sh(["cp", "-Rc", str(src), str(dest)])
        if code == 0:
            return
        shutil.rmtree(dest, ignore_errors=True)
    shutil.copytree(src, dest, dirs_exist_ok=True)


RUNNER = r'''
import sys, json, traceback
sys.path.insert(0, sys.argv[1])
sys.dont_write_bytecode = True
ns = {}
try:
    exec(compile(open(sys.argv[2], encoding="utf-8").read(), sys.argv[2], "exec"), ns)
    out = ns["run"]()
    print(json.dumps({"ok": True, "result": out if isinstance(out, str) else repr(out)}))
except BaseException as e:
    print(json.dumps({"ok": False, "error": type(e).__name__, "message": str(e)[:300],
                      "where": traceback.format_exc().splitlines()[-3:]}))
'''

MISSING = ("ImportError", "AttributeError", "ModuleNotFoundError", "NameError")


def run_snippet(tree: Path, snippet: Path, home: Path, timeout: float = 60, import_root: str = "") -> Dict[str, Any]:
    """Run `run()` of a snippet file with `tree` first on the import path. A separate process, no bytecode.

    `import_root`: the folder inside `tree` that holds the top-level package, for example `src`."""
    home.mkdir(parents=True, exist_ok=True)
    code, out, err = run_group([sys.executable, "-I", "-c", RUNNER, str(tree / import_root), str(snippet)], tree, timeout,
                               env=snippet_env(home))
    if code is None:
        return {"ok": False, "error": "timeout", "message": f"run() did not return in {timeout} seconds"}
    line = [x for x in out.splitlines() if x.startswith("{")]
    try:
        return json.loads(line[-1]) if line else {"ok": False, "error": "no output", "message": err[-300:]}
    except ValueError:
        return {"ok": False, "error": "no output", "message": line[-1][:300]}


def apply_cost_rule(steps: List[Dict[str, Any]]) -> Optional[Dict[str, float]]:
    """Set `cost_usd` of each visit and return the cost of each node, or None when a cost is unknown.

    The provider tool reports the cost of a resumed session as the total of the session so far.
    So the cost of a node is the largest value of its visits, and the cost of one visit is the
    difference from the visit before it. A visit that ran a job and has no reported cost makes the
    total unknown: 0 would be a false number.
    """
    node_cost: Dict[str, float] = {}
    unknown = False
    for s in steps:
        if "reported_usd" not in s:
            continue
        reported = s["reported_usd"]
        if reported is None:
            s["cost_usd"] = None
            unknown = True
            continue
        before = node_cost.get(s["node"], 0.0)
        s["cost_usd"] = round(max(0.0, reported - before), 6)
        node_cost[s["node"]] = max(before, reported)
    return None if unknown else {k: round(v, 6) for k, v in node_cost.items()}


def is_test_file(path: str) -> bool:
    parts = Path(path).parts
    name = parts[-1] if parts else path
    return (any(p in ("tests", "test", "testing") for p in parts[:-1]) or name.startswith("test_")
            or name.endswith("_test.py") or name == "conftest.py")
