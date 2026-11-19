"""Pins: the SHA-256 of each author file and each generated file."""
from __future__ import annotations

import hashlib
import json

from hpflow.proof.domain import AUTHOR_FILES, GEN_DIR, LOCK_FILE, Domain
from hpflow.proof.generate import generate, generated_texts


def sha(path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pinned_paths(domain: Domain) -> list:
    ns = domain.config()["namespace"]
    return AUTHOR_FILES + [f"{GEN_DIR}/{name}" for name in sorted(generated_texts(ns))]


def current(domain: Domain) -> dict:
    out = {}
    for rel in pinned_paths(domain):
        path = domain.path(rel)
        out[rel] = sha(path) if path.exists() else None
    return out


def pin(domain: Domain) -> dict:
    generate(domain)
    hashes = current(domain)
    data = {"tool": "hardproof", "files": hashes}
    domain.path(LOCK_FILE).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {"command": "pin", "verdict": "accept", "lock": str(domain.path(LOCK_FILE)), "files": hashes}


def verify(domain: Domain, expect: list) -> dict:
    report = {"command": "verify-pins", "verdict": "reject", "problems": []}
    wanted = {}
    lock = domain.path(LOCK_FILE)
    if expect:
        for item in expect:
            if "=" not in item:
                report["problems"].append(f"`{item}` is not FILE=SHA")
                continue
            name, value = item.split("=", 1)
            wanted[name] = value.strip().lower()
        report["source"] = "expect"
    elif lock.exists():
        wanted = json.loads(lock.read_text(encoding="utf-8")).get("files", {})
        report["source"] = LOCK_FILE
    else:
        report["problems"].append(f"{LOCK_FILE} does not exist and no --expect value is given")
        return report
    changed = []
    for rel, value in sorted(wanted.items()):
        path = domain.path(rel)
        now = sha(path) if path.exists() else None
        if now != value:
            changed.append({"file": rel, "pinned": value, "now": now})
    report["checked"] = len(wanted)
    report["changed"] = changed
    if changed:
        report["problems"] += [f"{c['file']} differs from its pin" for c in changed]
    if not report["problems"]:
        report["verdict"] = "accept"
    return report
