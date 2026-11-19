#!/usr/bin/env python3
"""Hard Proof v2: the measured data of hpflow 0.5.0 in one file, `release_050.json`.

Each number comes from a stored folder: the records of an audit (`hpf` writes one for each worker session), the
gate report of that audit, the scores of `levers.py`, and `h2h/result.json`. This script makes no model call.

Usage:
    python3 release_050.py --ref <release commit>
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path

from bugs import WORK

HERE = Path(__file__).resolve().parent
REPO = Path.home() / "Projects" / "hard-proof-repo"
SELF = [("audit-hpflow-self-full", "The release range"), ("audit-hpflow-self-delta", "The fixes of round 1"),
        ("audit-hpflow-self-delta2", "The fixes of round 2"), ("audit-hpflow-self-delta3", "The fixes of round 3"),
        ("audit-hpflow-self-delta4", "The fixes of round 4"), ("audit-hpflow-self-delta5", "The fixes of round 5"),
        ("audit-hpflow-self-delta6", "The fixes of round 6")]
SAME_RANGE = [("audit-pm-1510-lean", "hpflow 0.4.2: lean workers, all tools of Claude Code"),
              ("audit-pm-1510-toolsonly", "hpflow 0.5.0: six tools, medium effort"),
              ("audit-pm-1510-toolsonly2", "hpflow 0.5.0: six tools, medium effort (run 2)"),
              ("audit-pm-1510-toolsonly3", "hpflow 0.5.0: six tools, medium effort (run 3)")]
LIVE = [("hpflow-direct-live/claude5", "Claude Code"), ("hpflow-direct-live/codex5", "Codex"),
        ("hpflow-command-live/audit", "the command adapter (the tool <code>opencode</code> with a model of OpenRouter)")]


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def stamp(text: str) -> float:
    return datetime.fromisoformat(text).timestamp()


def audit(folder: Path) -> dict:
    """The numbers of one audit folder, from its records."""
    records = [load(p) for p in sorted((folder / "records").glob("*.json"))]
    records = [r for r in records if r and r.get("kind") in ("review", "verify")]
    review = load(folder / "review.json") or {}
    confirmed = load(folder / "confirmed.json")
    targets = load(folder / "targets.json") or {}
    spans = [(stamp(r["finished"]) - (r.get("seconds") or 0), stamp(r["finished"])) for r in records if r.get("finished")]
    cost = {kind: [r.get("cost_usd") for r in records if r["kind"] == kind] for kind in ("review", "verify")}

    def total(values: list):
        return None if any(v is None for v in values) else round(sum(values), 2)

    severities: dict = {}
    for bug in confirmed or []:
        severities[bug.get("severity") or "none"] = severities.get(bug.get("severity") or "none", 0) + 1
    return {"folder": folder.name, "commit": (load(folder / "audit.json") or {}).get("commit", "")[:7],
            "range": targets.get("changed"), "targets": len(targets.get("targets") or []),
            "findings": len(review.get("findings") or []), "confirmed_bugs": len(confirmed or []),
            "confirmed_by_severity": severities,
            "review_sessions": len(cost["review"]), "verifier_sessions": len(cost["verify"]),
            "review_cost_usd": total(cost["review"]), "verify_cost_usd": total(cost["verify"]),
            "cost_usd": total(cost["review"] + cost["verify"]),
            "worker_seconds": sum(r.get("seconds") or 0 for r in records),
            "wall_seconds": round(max(b for _, b in spans) - min(a for a, _ in spans)) if spans else None}


def gate(folder: Path, ref: str) -> dict:
    p = subprocess.run(["hpf", "gate", "--out", str(folder), "--ref", ref], cwd=REPO, capture_output=True, text=True)
    report = json.loads(p.stdout)
    return {"verdict": report["verdict"], "closed": report.get("closed"), "open": len(report.get("open") or []),
            "waived": report.get("waived")}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ref", required=True)
    args = parser.parse_args()
    commit = subprocess.run(["git", "-C", str(REPO), "rev-parse", args.ref], capture_output=True, text=True).stdout.strip()

    rounds = []
    for n, (name, what) in enumerate(SELF, 1):
        folder = WORK / name
        if not (folder / "confirmed.json").exists():
            continue
        rounds.append(dict(audit(folder), round=n, what=what, gate=gate(folder, commit)))
        # The report of the round and its confirmed bugs go into the study as evidence.
        keep = HERE / "self_audit" / f"round_{n}"
        keep.mkdir(parents=True, exist_ok=True)
        for name in ("REPORT.md", "confirmed.json", "targets.json", "waivers.json"):
            if (folder / name).exists():
                shutil.copyfile(folder / name, keep / name)
    score, other = load(HERE / "levers" / "score.json"), load(HERE / "levers" / "score_other.json")
    arms = {"lean": "hpflow 0.4.2 arguments, first 48 bugs", "direct_final": "hpflow 0.5.0 defaults, all 95 bugs",
            "tools": "the same arguments through a Puppetmaster flow (0.4 runner), all 95 bugs",
            "tools_short": "the short reviewer prompt (an option), all 95 bugs", "effort_low": "low effort, first 48 bugs",
            "haiku": "Haiku 5.5 as reviewer, first 48 bugs"}
    known = [{"arm": arm, "what": what, "bugs": score[arm]["runs"], "detected": score[arm]["detected"],
              "other_findings_changed_later": other[arm]["other_changed_later"], "cost_usd": score[arm]["cost_usd"],
              # The first sample of 48 bugs (seed 1), which each arm has.
              "first_48": {k: other[arm]["first"][k] for k in ("runs", "detected", "other_changed_later", "cost_usd")}}
             for arm, what in arms.items() if arm in score]
    h2h = load(HERE / "h2h" / "result.json") or {}
    data = {"version": "0.5.0", "commit": commit[:7],
            "self_audit": {"rounds": rounds,
                           "confirmed_bugs": sum(r["confirmed_bugs"] for r in rounds),
                           "closed_by_repro": sum(r["gate"]["closed"] or 0 for r in rounds),
                           "waived": sum(r["gate"]["waived"] or 0 for r in rounds),
                           "cost_usd": round(sum(r["cost_usd"] or 0 for r in rounds), 2)},
            "same_range": [dict(audit(WORK / name), setting=what) for name, what in SAME_RANGE if (WORK / name / "records").is_dir()],
            "known_bugs": known,
            # Two passes with one set of worker arguments on all 95 bugs: one through each runner.
            "two_passes": {"arms": ["tools", "direct"],
                           "each": [score["tools"]["detected"], score["direct"]["detected"]],
                           "together": len(set(score["tools"]["detected_ids"]) | set(score["direct"]["detected_ids"]))},
            "live_runs": [dict(audit(WORK / name), adapter=adapter) for name, adapter in LIVE if (WORK / name / "records").is_dir()],
            "head_to_head": {k: h2h.get(k) for k in ("range", "arms", "union_distinct_bugs", "verifier_cost_usd", "runs")}}
    (HERE / "release_050.json").write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"rounds": [(r["round"], r["targets"], r["findings"], r["confirmed_bugs"], r["cost_usd"], r["wall_seconds"],
                                  r["gate"]["verdict"]) for r in rounds],
                      "same_range": [(r["folder"], r["findings"], r["confirmed_bugs"], r["cost_usd"], r["wall_seconds"])
                                     for r in data["same_range"]],
                      "live": [(r["adapter"], r["targets"], r["confirmed_bugs"], r["cost_usd"]) for r in data["live_runs"]]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
