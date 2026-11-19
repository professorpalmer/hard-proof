"""Calls to `lake` and `lean` in the generated project folder."""
from __future__ import annotations

import os
import re
import shutil
import signal
import subprocess
import threading
import time
from pathlib import Path

PERMITTED = {"propext", "Quot.sound", "Classical.choice"}


MAX_RSS_GB = float(os.environ.get("HARDPROOF_MAX_RSS_GB", "8"))


def _group_rss_gb(pgid: int) -> float:
    """The resident memory of each process in a process group, in GB."""
    try:
        out = subprocess.run(["ps", "-A", "-o", "pgid=,rss="], capture_output=True, text=True, timeout=10).stdout
    except Exception:
        return 0.0
    total = 0
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == str(pgid):
            total += int(parts[1])
    return total / 1048576.0


def run(cmd: list, cwd: Path, stdin: str = None, timeout: float = 1800) -> tuple:
    """Run a command. Return (exit code, stdout, stderr).

    The command runs in its own process group with a memory limit (`HARDPROOF_MAX_RSS_GB`, default 8).
    A kernel on a pathological proof term can take more memory than the machine has, so the group is
    stopped at the limit. Exit code 137 with the text `memory limit` is a resource result, not a verdict.
    """
    try:
        proc = subprocess.Popen(cmd, cwd=str(cwd), stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    except FileNotFoundError as exc:
        return 127, "", f"command not found: {exc}"
    result: dict = {}

    def reader():
        try:
            result["out"], result["err"] = proc.communicate(stdin)
        except Exception as exc:  # the process group was stopped
            result.setdefault("out", "")
            result.setdefault("err", str(exc))

    thread = threading.Thread(target=reader, daemon=True)
    thread.start()
    started = time.time()
    reason = ""
    while thread.is_alive():
        thread.join(1.0)
        if not thread.is_alive():
            break
        if time.time() - started > timeout:
            reason = f"timeout after {timeout} seconds"
        elif _group_rss_gb(proc.pid) > MAX_RSS_GB:
            reason = f"memory limit: the process group used more than {MAX_RSS_GB:g} GB"
        if reason:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            thread.join(10)
            return (124 if reason.startswith("timeout") else 137), result.get("out", "") or "", reason
    return proc.returncode, result.get("out", "") or "", result.get("err", "") or ""


def clean(text: str, limit: int = 4000) -> str:
    """Remove the trace lines of lake and keep the last part of the output."""
    keep = [l for l in text.splitlines() if not l.startswith(("trace:", "Exporting #["))]
    return "\n".join(keep)[-limit:]


def build(gen: Path, target: str) -> tuple:
    """Build one lake target. Return (ok, output)."""
    rc, out, err = run(["lake", "build", target], gen)
    return rc == 0, clean(out + err)


def probe(gen: Path, name: str, text: str) -> tuple:
    """Elaborate a probe file in `.lake/hardproof`. Return (exit code, output)."""
    folder = gen / ".lake" / "hardproof"
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / f"{name}.lean"
    path.write_text(text, encoding="utf-8")
    rc, out, err = run(["lake", "env", "lean", str(path)], gen)
    return rc, out + err


def error_lines(output: str, probe_name: str) -> dict:
    """Map each line number of a probe file to its error messages."""
    errors: dict = {}
    # Lean 4.36 writes `error(<class>): message`; older versions write `error: message`.
    pattern = re.compile(rf"{re.escape(probe_name)}\.lean:(\d+):\d+: error(?:\([^)]*\))?: (.*)")
    for line in output.splitlines():
        m = pattern.search(line)
        if m:
            errors.setdefault(int(m.group(1)), []).append(m.group(2))
    return errors


def axioms(output: str) -> dict:
    """Parse `#print axioms` output into {declaration: [axioms]}."""
    found: dict = {}
    text = output.replace("\n", " ")
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        found[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        found[m.group(1)] = []
    return found


def comparator(gen: Path, config: str, paranoid: bool) -> tuple:
    """Run `lake comparator`. Return (exit code, output, flags)."""
    cmd = ["lake", "comparator", "--config", config]
    flags = []
    if paranoid:
        flags.append("--paranoid")
    if shutil.which("bwrap") is None:
        flags.append("--inadvisably-no-sandbox")
    rc, out, err = run(cmd + flags, gen)
    return rc, clean(out + err), flags


def strip_comments(text: str) -> str:
    """Remove Lean comments (nested block comments too) and string bodies stay."""
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                break
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def word(text: str, w: str) -> bool:
    """True when `w` occurs as a whole name or as the last part of a dotted name."""
    text = text.replace("«", "").replace("»", "")
    return re.search(rf"(?<![A-Za-z0-9_'!?]){re.escape(w)}(?![A-Za-z0-9_'!?])", text) is not None


def forbidden(code: str) -> list:
    """The text rules for files that must have no hole and no new axiom."""
    problems = []
    for w in ("sorry", "native_decide", "admit"):
        if word(code, w):
            problems.append(f"the file uses `{w}`")
    if re.search(r"(^|\s)axiom\s", code):
        problems.append("the file declares an axiom")
    if word(code, "implemented_by") or word(code, "extern"):
        problems.append("the file uses `implemented_by` or `extern`")
    return problems


def imports(code: str) -> list:
    return re.findall(r"^\s*import\s+([A-Za-z0-9_.]+)", code, flags=re.M)
