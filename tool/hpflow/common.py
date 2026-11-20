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
import tempfile
import threading
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
    if not WINDOWS:
        return shlex.quote(text)
    quoted = subprocess.list2cmdline([text])
    # list2cmdline quotes only for spaces, but cmd.exe splits a bare argument at & | < > ^.
    if not quoted.startswith('"') and any(c in quoted for c in "&|<>^"):
        # A closing quote after a backslash would be read as an escaped quote, so each trailing backslash doubles.
        tail = len(quoted) - len(quoted.rstrip("\\"))
        quoted = '"' + quoted + "\\" * tail + '"'
    return quoted


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


def venv_python(root: Path) -> Optional[Path]:
    """The Python of the venv `.venv` in `root`, or None. A venv on Windows keeps it in `Scripts`."""
    path = root / ".venv" / ("Scripts/python.exe" if WINDOWS else "bin/python")
    return path if path.is_file() else None


def project_python(python: Optional[str]) -> str:
    """The Python of the project under audit (the key `python` of audit.json). It runs each repro, so a repro can
    import the dependencies of the project.

    There is no fallback to the Python of hpflow: that Python often cannot import a dependency of the project, and
    a repro that cannot import its code counts as no answer. So a bad value is a usage error that names the repair."""
    repair = "run `hpf init` again with the same --repo and --ref, and give --python"
    if not python:
        raise UsageError(f"audit.json has no `python` (the Python that runs the repros): {repair}")
    if not os.path.isfile(python) or not os.access(python, os.X_OK):
        raise UsageError(f"the Python of the project {python} does not exist or cannot run: {repair}")
    return python


def shim_texts(python: str, windows: bool) -> Dict[str, str]:
    """The files of the shim folder: `python3` and `python` start `python` with the same arguments. A script, not a
    symbolic link: Python finds its venv from `pyvenv.cfg` beside the path that started it, so a link from another
    folder does not load the venv. On Windows the files are `.cmd` files."""
    if windows:
        line = '@"' + python.replace("%", "%%") + '" %*\r\n'
        return {"python3.cmd": line, "python.cmd": line}
    text = "#!/bin/sh\nexec " + shlex.quote(python) + ' "$@"\n'
    return {"python3": text, "python": text}


def write_python_shims(folder: Path, python: str) -> Path:
    """Write the shim folder of `python` (see `shim_texts`) and return it. Parallel workers can call it: a file
    that has the right text stays, and a new file comes into place in one rename."""
    folder.mkdir(parents=True, exist_ok=True)

    def right(path: Path, data: bytes) -> bool:
        # Bytes, not text: a text read turns the CRLF of a .cmd file into LF, and the file would never match.
        try:
            return path.read_bytes() == data and (WINDOWS or os.access(path, os.X_OK))
        except OSError:
            return False

    for name, text in shim_texts(python, WINDOWS).items():
        path, data = folder / name, text.encode("utf-8")
        if right(path, data):
            continue
        tmp = folder / f".{name}.{os.getpid()}.{threading.get_ident()}"
        tmp.write_bytes(data)
        tmp.chmod(0o755)
        try:
            os.replace(tmp, path)
        except OSError:
            # Windows refuses to replace a file that another worker runs. Another call wrote the same text, so it
            # is not an error.
            tmp.unlink(missing_ok=True)
            if not right(path, data):
                raise
    return folder


def find_python(python: Optional[str], root: Path) -> str:
    """The Python that `init` stores: `--python` (a bare name is found on PATH), else the venv of the repository,
    else the Python of hpflow. The value is an absolute path, because a repro runs with a small PATH. A symbolic
    link stays as it is: the link of a venv is what makes it a venv."""
    if python is None:
        venv = venv_python(root)
        path = str(venv) if venv else sys.executable
    else:
        found = shutil.which(python)
        if not found:
            raise UsageError(f"--python {python}: no such program")
        path = os.path.abspath(found)
    try:
        p = subprocess.run([path, "-I", "-c", "import sys; print(sys.version_info[0])"], capture_output=True,
                           text=True, timeout=60)
        major = p.stdout.strip() if p.returncode == 0 else ""
    except (OSError, subprocess.SubprocessError):
        major = ""
    if major != "3":
        raise UsageError(f"the Python {path} does not run or is not Python 3: give --python")
    return path


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
              env: Optional[Dict[str, str]] = None, stdin: Optional[str] = None,
              exact: bool = False) -> Tuple[Optional[int], str, str]:
    """Run a command in its own process group. At the timeout the whole group ends.

    `stdin` is the text on the standard input; with None the input is empty.
    `exact`: the output keeps each carriage return. Without it the output has the newlines of text mode.
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
    # Threads read the pipes, so the wait ends when the leader exits, not when the last holder of a pipe closes it:
    # a child left in the background can hold the pipes open until the timeout.
    chunks: Tuple[List[bytes], List[bytes]] = ([], [])
    threads = [threading.Thread(target=_drain, args=(s, c), daemon=True) for s, c in zip((p.stdout, p.stderr), chunks)]
    if stdin is not None:
        threads.append(threading.Thread(target=_feed, args=(p.stdin, stdin.encode("utf-8")), daemon=True))
    for t in threads:
        t.start()
    try:
        code: Optional[int] = p.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        code = None
    except BaseException:
        kill_group(p)
        p.wait()
        raise
    # The leader can exit while a child of its group still runs. That child must end too.
    kill_group(p)
    p.wait()
    for t in threads:
        t.join(DRAIN_TIMEOUT)
    return code, decode(b"".join(chunks[0]), exact), decode(b"".join(chunks[1]), exact)


# Seconds to read the rest of the output after the group ends. A child outside the group can hold a pipe open.
DRAIN_TIMEOUT = 5


def _drain(stream: Any, chunks: List[bytes]) -> None:
    try:
        while True:
            data = stream.read1(65536)
            if not data:
                return
            chunks.append(data)
    except (OSError, ValueError):
        pass


def _feed(stream: Any, data: bytes) -> None:
    # The command may exit without reading its input.
    try:
        stream.write(data)
        stream.close()
    except (OSError, ValueError):
        pass


def decode(data: Optional[bytes], exact: bool = False) -> str:
    """Output as UTF-8 with replacement. As text mode reads it, each `\r\n` or `\r` becomes `\n`. With `exact`
    each character stays: a file name or a file from git can have a carriage return."""
    text = (data or b"").decode("utf-8", "replace")
    return text if exact else text.replace("\r\n", "\n").replace("\r", "\n")


def sh(cmd: List[str], cwd: Optional[Path] = None, timeout: float = 600) -> Tuple[int, str]:
    code, out, err = run_group(cmd, cwd, timeout)
    if code is None:
        return 124, "timeout"
    return code, out + err


def lines_of(text: str) -> List[str]:
    """The lines of a text from a tool or a file. Only "\n" ends a line.

    `str.splitlines` also ends a line at a form feed, at U+001C to U+001E, at U+0085 and at U+2028 and U+2029.
    Such a character in a file name, a string value or a changed line is content, so each reader of outside
    text uses this function."""
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines


def git(repo: Path, *args: str, timeout: float = 600) -> Tuple[int, str]:
    """Run git in `repo`. Each path that a command gets after "--" is a literal name, not a pattern: a file can
    have "*", "?" or "[" in its name. The output is exact: git ends its own lines with a line feed on each system,
    and a carriage return in a name or in a file is content."""
    code, out, err = run_group(["git", "-C", str(repo), *args], timeout=timeout,
                               env=dict(os.environ, GIT_LITERAL_PATHSPECS="1"), exact=True)
    if code is None:
        return 124, "timeout"
    return code, out if code == 0 else out + err


def git_status(tree: Path) -> Optional[List[Dict[str, Optional[str]]]]:
    """Each entry of `git status` in a work tree: the two status letters, the path and, for a rename or a copy,
    the source path. None when git fails.

    The list comes from `--porcelain=v1 -z`, which has NUL between the fields and does not quote a name. So a
    name with a space, a quote, a line break or a non-ASCII character is the real name."""
    code, out = git(tree, "status", "--porcelain=v1", "-z", "--untracked-files=all", timeout=120)
    if code != 0:
        return None
    fields = out.split("\0")
    entries: List[Dict[str, Optional[str]]] = []
    i = 0
    while i < len(fields):
        field = fields[i]
        i += 1
        if len(field) < 4:
            continue
        source = None
        if "R" in field[:2] or "C" in field[:2]:
            # A rename or a copy, in the index or in the work tree, has its source path in the next field.
            source = fields[i] if i < len(fields) and fields[i] else None
            i += 1
        entries.append({"status": field[:2], "path": field[3:], "source": source})
    return entries


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
root, path, result_file = sys.argv[1:4]
sys.path.insert(0, root)
sys.dont_write_bytecode = True
ns = {}
try:
    exec(compile(open(path, encoding="utf-8").read(), path, "exec"), ns)
    out = ns["run"]()
    result = {"ok": True, "result": out if isinstance(out, str) else repr(out)}
except BaseException as e:
    result = {"ok": False, "error": type(e).__name__, "message": str(e)[:300],
              "where": traceback.format_exc().split("\n")[-4:-1]}
with open(result_file, "w", encoding="utf-8") as handle:
    json.dump(result, handle)
'''

MISSING = ("ImportError", "AttributeError", "ModuleNotFoundError", "NameError")
# A repro with one of these results did not run to an answer, so it says nothing about the code.
NO_ANSWER = ("timeout", "no output") + MISSING


def run_snippet(tree: Path, snippet: Path, home: Path, python: str, timeout: float = 60,
                import_root: str = "") -> Dict[str, Any]:
    """Run `run()` of a snippet file with `tree` first on the import path. A separate process, no bytecode.

    `python`: the Python of the project (see `project_python`). RUNNER must run on each Python 3 that a project can
    have, so it uses no new syntax.

    `import_root`: the folder inside `tree` that holds the top-level package, for example `src`.
    The child writes its result to a file of its own. So text that the snippet or the code under test prints
    is not read as the result."""
    home.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="hpflow-repro-") as tmp:
        result_file = Path(tmp) / "result.json"
        # The child runs in `tree`, so each path that it gets is absolute.
        code, _, err = run_group([python, "-I", "-c", RUNNER, str((tree / import_root).resolve()),
                                  str(snippet.resolve()), str(result_file)], tree, timeout, env=snippet_env(home))
        if code is None:
            return {"ok": False, "error": "timeout", "message": f"run() did not return in {timeout} seconds"}
        try:
            result = json.loads(result_file.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            result = None
    if not isinstance(result, dict) or not isinstance(result.get("ok"), bool):
        # The process ended before it wrote a result: the snippet or the code under test stopped the interpreter.
        return {"ok": False, "error": "no output", "message": err[-300:]}
    return result


def repro_state(got: Dict[str, Any], result_before: str) -> str:
    """What a repro says about the code after a change. `got` is the result of `run_snippet` on the new code, and
    `result_before` is what `run()` gave on the code under audit.

    "same": the old result, so the bug is there. "new": another result, or an exception of the code under test.
    "unknown": the repro did not run to an answer (a timeout, a name that the new code does not have, or no
    result), so it does not show that the bug is closed."""
    if got.get("ok"):
        return "same" if got.get("result") == result_before else "new"
    return "unknown" if got.get("error") in NO_ANSWER else "new"


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
