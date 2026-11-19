"""A lean CODEX_HOME for Codex workers, as Puppetmaster 1.52.0 gives one (puppetmaster/codex_home.py).

A fresh `codex exec` sends a start block that Codex builds from CODEX_HOME: the skills list, plugin text and
MCP context of the user. A bounded worker needs none of it. On this Mac the first request of a worker was
21,974 input tokens with the home of the user and 14,490 with the lean home (codex-cli 0.160.0, 2026-11-19);
most of the difference was the skills list (28,326 against 2,875 characters).

The lean home keeps the settings of the user (model, providers, profiles) and the global AGENTS.md, and drops
the tables `mcp_servers`, `plugins`, `marketplaces`, `memories`, `hooks` and the key `notify`. auth.json is
copied, never linked: Codex refreshes a ChatGPT login by replacing auth.json, which would orphan the refresh
token of the user. A refreshed auth.json goes back only when the file of the user did not change since the copy.
"""
from __future__ import annotations

import hashlib
import os
import re
import shutil
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import IO, Iterator, Optional

from .common import run_group

DROPPED_TABLE = re.compile(r"^\[\[?\s*(mcp_servers|plugins|marketplaces|memories|hooks)\b")
DROPPED_TOP_KEYS = ("notify",)
# The orchestration block that `puppetmaster install-rules` writes into AGENTS.md. It tells a pilot to delegate,
# and only costs a worker context.
PM_BEGIN, PM_END = "<!-- puppetmaster:rules:begin -->", "<!-- puppetmaster:rules:end -->"
SEED_TIMEOUT = 15


def user_home() -> Path:
    explicit = (os.environ.get("CODEX_HOME") or "").strip()
    return Path(explicit).expanduser() if explicit else Path.home() / ".codex"


def worker_home() -> Path:
    explicit = (os.environ.get("HPFLOW_CODEX_HOME") or "").strip()
    return Path(explicit).expanduser() if explicit else Path.home() / ".hpflow" / "codex-worker-home"


def lean_config(text: str) -> str:
    """The config.toml of the user without the tables and keys a worker must not inherit."""
    out = []
    dropping = False
    skip_depth = 0
    # A kept multi-line array can have lines that start with "[", which are not table headers either.
    kept_depth = 0
    in_table = False
    for line in text.splitlines():
        stripped = line.strip()
        if skip_depth:
            skip_depth += stripped.count("[") - stripped.count("]")
            continue
        if kept_depth and not DROPPED_TABLE.match(stripped):
            # A dropped table ends the value, so a miscounted bracket never lets that table through.
            kept_depth += stripped.count("[") - stripped.count("]")
            out.append(line)
            continue
        kept_depth = 0
        if stripped.startswith("["):
            in_table = True
            dropping = bool(DROPPED_TABLE.match(stripped))
            if dropping:
                continue
        if dropping:
            # A multi-line value can have lines that start with "[", which are not table headers.
            depth = stripped.count("[") - stripped.count("]")
            skip_depth = depth if depth > 0 else 0
            continue
        key = stripped.split("=", 1)[0].strip() if "=" in stripped else ""
        if key in DROPPED_TOP_KEYS and not in_table:
            depth = stripped.count("[") - stripped.count("]")
            skip_depth = depth if depth > 0 else 0
            continue
        out.append(line)
        if key and not stripped.startswith("[") and stripped.split("=", 1)[1].strip().startswith("["):
            kept_depth = max(stripped.count("[") - stripped.count("]"), 0)
    return "\n".join(out) + "\n"


def strip_pm_block(text: str) -> str:
    begin, end = text.find(PM_BEGIN), text.find(PM_END)
    if begin == -1 or end == -1 or end < begin:
        return text
    stop = text.find("\n", end)
    return text[:begin] + text[(len(text) if stop == -1 else stop + 1):]


def digest(path: Path) -> Optional[str]:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def write_atomic(path: Path, data: bytes, mode: int = 0o600) -> None:
    tmp = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, mode)
    with os.fdopen(fd, "wb") as handle:
        handle.write(data)
    os.replace(tmp, path)


@contextmanager
def locked(home: Path) -> Iterator[None]:
    """One process at a time changes the lean home or copies auth.json."""
    home.mkdir(parents=True, exist_ok=True)
    with open(home / ".sync.lock", "a+") as handle:
        lock_file(handle, True)
        try:
            yield
        finally:
            lock_file(handle, False)


def lock_file(handle: IO[str], take: bool) -> None:
    """Take or release an exclusive lock on an open file. It waits until the lock is free."""
    if os.name == "nt":
        import msvcrt

        handle.seek(0)
        while True:
            try:
                # LK_LOCK tries for about 10 seconds, then raises. One byte at the start is the lock.
                msvcrt.locking(handle.fileno(), msvcrt.LK_LOCK if take else msvcrt.LK_UNLCK, 1)  # type: ignore[attr-defined]
                return
            except OSError:
                if not take:
                    return
    else:
        import fcntl

        fcntl.flock(handle, fcntl.LOCK_EX if take else fcntl.LOCK_UN)


def prepare(codex: str) -> Optional[Path]:
    """Make or refresh the lean home. None: the user has no auth.json, so the worker uses the home of the user."""
    source = user_home()
    if not (source / "auth.json").is_file():
        return None
    home = worker_home()
    with locked(home):
        try:
            config = (source / "config.toml").read_text(encoding="utf-8")
        except OSError:
            config = ""
        lean = lean_config(config).encode("utf-8")
        if digest(home / "config.toml") != hashlib.sha256(lean).hexdigest():
            write_atomic(home / "config.toml", lean)
        agents = source / "AGENTS.md"
        if agents.is_file():
            raw = agents.read_bytes()
            try:
                data = strip_pm_block(raw.decode("utf-8")).encode("utf-8")
            except UnicodeDecodeError:
                data = raw
            if digest(home / "AGENTS.md") != hashlib.sha256(data).hexdigest():
                write_atomic(home / "AGENTS.md", data, 0o644)
        else:
            # The user removed their AGENTS.md, so the worker must not keep the old copy.
            (home / "AGENTS.md").unlink(missing_ok=True)
        user_auth = digest(source / "auth.json")
        synced = (home / ".auth.synced").read_text(encoding="utf-8") if (home / ".auth.synced").exists() else None
        if user_auth != synced:
            write_atomic(home / "auth.json", (source / "auth.json").read_bytes())
            (home / ".auth.synced").write_text(user_auth or "", encoding="utf-8")
        seed_system_skills(home, codex)
    return home


def sync_back(home: Path) -> bool:
    """Copy a refreshed auth.json back to the home of the user, only when theirs did not change."""
    source = user_home()
    with locked(home):
        marker = home / ".auth.synced"
        synced = marker.read_text(encoding="utf-8") if marker.exists() else None
        worker = digest(home / "auth.json")
        if not synced or worker in (None, synced) or digest(source / "auth.json") != synced:
            return False
        write_atomic(source / "auth.json", (home / "auth.json").read_bytes())
        marker.write_text(worker or "", encoding="utf-8")
        return True


def seed_system_skills(home: Path, codex: str) -> None:
    """Install the builtin skill bundle of Codex once, before parallel workers start in the home.

    Each Codex start installs the bundle when its marker is missing, and parallel starts in one fresh home
    left a partial bundle (puppetmaster/codex_home.py, `ensure_system_skills`). This installs it with
    `codex debug prompt-input` in a home with no credentials, and copies it in. Called with the lock held."""
    target = home / "skills" / ".system"
    if any(target.glob(".*marker")):
        return
    with tempfile.TemporaryDirectory(prefix="hpflow-codex-seed-") as tmp:
        env = {k: v for k, v in os.environ.items() if not k.endswith("_API_KEY")}
        env["CODEX_HOME"] = tmp
        code, _, _ = run_group([codex, "debug", "prompt-input", "."], Path(tmp), SEED_TIMEOUT, env=env)
        if code != 0:
            return
        bundle = Path(tmp) / "skills" / ".system"
        if not any(bundle.glob(".*marker")):
            return
        shutil.rmtree(target, ignore_errors=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(bundle, target)
