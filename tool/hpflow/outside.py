"""The findings of a reviewer outside hpflow, read into one form.

A finding of another tool has no repro, so it is not a finding of the ladder. This module only reads it:
the file, the place in the file (a function name, a line, or the two), the claim text and the name of the tool.
`commands.cmd_import` then gives each claim to a worker that must show it with a repro.

Two input forms:

- The hpflow form: a JSON list, or an object with the key `findings`. Each entry is an object with `file`,
  `claim`, and `function` or `line` (or the two). `source` is optional.
- SARIF 2.1.0 (an object with the key `runs`): each result of each run, with its message, the first location
  and the name of the tool.

A file that is not one of these forms is a usage error. An entry that this module cannot read is not an error
of the call: the entry gets a reason and goes into the list of skipped entries, because the output of another
tool is not in our hands.
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import unquote, urlsplit

from .common import UsageError

MAX_CLAIM = 4000
Entry = Dict[str, Any]


def text_of(value: Any) -> Optional[str]:
    """A text with content, or None."""
    return value.strip() if isinstance(value, str) and value.strip() else None


def line_of(value: Any) -> Optional[int]:
    """A line number of 1 or more, or None. `True` is not a line number."""
    return value if isinstance(value, int) and not isinstance(value, bool) and value >= 1 else None


def entry(index: int, raw: Any, source: Optional[str]) -> Tuple[Optional[Entry], Optional[str]]:
    """One entry of the hpflow form: the entry, or the reason why it is skipped."""
    if not isinstance(raw, dict):
        return None, "the entry is not an object"
    claim, file = text_of(raw.get("claim")), text_of(raw.get("file"))
    if claim is None:
        return None, "no claim text"
    if file is None:
        return None, "no file"
    function, line = text_of(raw.get("function")), line_of(raw.get("line"))
    if function is None and line is None:
        return None, "no function name and no line"
    return {"index": index, "file": file, "function": function, "line": line, "claim": claim[:MAX_CLAIM],
            "source": text_of(raw.get("source")) or source or "outside"}, None


def file_of_uri(uri: str) -> str:
    """The path of a SARIF artifact location. A `file:` address gives its path, and each `%XX` is decoded."""
    parts = urlsplit(uri)
    if parts.scheme == "file":
        path = unquote(parts.path)
        if re.fullmatch(r"[A-Za-z]:", parts.netloc):
            # `file://C:/x.py` has the drive in the place of the host.
            return parts.netloc + path
        # `hostname` is the host in lower case and with no port: the name of a host has no case.
        if (parts.hostname or "") not in ("", "localhost"):
            # A file on another host. It is not a file of the repository.
            return f"//{parts.netloc}{path}"
        # `file:///C:/x.py` has the path `/C:/x.py`. The path on Windows is `C:/x.py`.
        return path[1:] if re.match(r"^/[A-Za-z]:", path) else path
    # A Windows path such as `C:\\x.py` has a one-letter scheme. It is a path, not an address.
    return unquote(uri) if not parts.scheme or len(parts.scheme) == 1 else uri


def sarif_result(index: int, result: Any, tool: str) -> Tuple[Optional[Entry], Optional[str]]:
    """One result of a SARIF run: the entry, or the reason why it is skipped."""
    if not isinstance(result, dict):
        return None, "the result is not an object"
    message = result.get("message") if isinstance(result.get("message"), dict) else {}
    text = text_of(message.get("text")) or text_of(message.get("markdown"))
    locations = result.get("locations") if isinstance(result.get("locations"), list) else []
    place = locations[0].get("physicalLocation") if locations and isinstance(locations[0], dict) else None
    place = place if isinstance(place, dict) else {}
    artifact = place.get("artifactLocation") if isinstance(place.get("artifactLocation"), dict) else {}
    region = place.get("region") if isinstance(place.get("region"), dict) else {}
    uri, line = text_of(artifact.get("uri")), line_of(region.get("startLine"))
    if text is None:
        return None, "no message text"
    if uri is None:
        return None, "no file in the first location"
    if line is None:
        return None, "no start line in the first location"
    try:
        file = file_of_uri(uri)
    except ValueError:
        # The address parser of Python refuses some texts, for example an open bracket in the host.
        return None, "the file address of the first location is not valid"
    rule = text_of(result.get("ruleId"))
    claim = f"{rule}: {text}" if rule else text
    return {"index": index, "file": file, "function": None, "line": line, "claim": claim[:MAX_CLAIM], "source": tool}, None


def sarif_entries(data: Dict[str, Any], source: Optional[str]) -> List[Tuple[Optional[Entry], Optional[str]]]:
    out: List[Tuple[Optional[Entry], Optional[str]]] = []
    for run in data.get("runs") or []:
        if not isinstance(run, dict):
            continue
        driver = ((run.get("tool") or {}).get("driver") or {}) if isinstance(run.get("tool"), dict) else {}
        # The name that the file gives comes first, as for an entry of the hpflow form.
        tool = text_of(driver.get("name") if isinstance(driver, dict) else None) or source or "outside"
        results = run.get("results") if isinstance(run.get("results"), list) else []
        for result in results:
            out.append(sarif_result(len(out), result, tool))
    return out


def read(path: Path, source: Optional[str] = None) -> Tuple[List[Entry], List[Dict[str, Any]]]:
    """The entries of one findings file and the skipped entries, each with its index in the file and a reason.

    `source` is the name of the tool for an entry that does not give one."""
    try:
        data = json.loads(path.read_text(encoding="utf-8-sig"))
    except OSError as e:
        raise UsageError(f"cannot read the findings file {path}: {e.strerror or e}") from None
    except (ValueError, RecursionError) as e:
        # A file that is not UTF-8 text gives a ValueError too. A file with very deep lists gives a RecursionError.
        raise UsageError(f"the findings file {path} is not JSON: {e}") from None
    if isinstance(data, dict) and isinstance(data.get("runs"), list):
        pairs = sarif_entries(data, source)
    else:
        items = data.get("findings") if isinstance(data, dict) else data
        if not isinstance(items, list):
            raise UsageError(f"the findings file {path} must be a JSON list, an object with the key `findings`, or SARIF")
        pairs = [entry(i, raw, source) for i, raw in enumerate(items)]
    entries = [e for e, _ in pairs if e is not None]
    skipped = [{"file": str(path), "index": i, "reason": why} for i, (e, why) in enumerate(pairs) if e is None]
    return entries, skipped
