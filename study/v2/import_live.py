#!/usr/bin/env python3
"""Hard Proof v2: the live test of `hpf import` on the findings of two other review tools.

The input is the two lists of `h2h` (10 findings of Claude Code review, 2 of Codex review, on Puppetmaster
`v1.50.0..v1.51.1`). Each run is `hpf audit --ref v1.51.1 --findings <the two lists>`: a worker must show each
claim with a repro, then two verifiers judge the claims with a repro. This script reads the two run folders and
writes `import_live.json`. It makes no model call.

Run 1 used the first brief of the import worker. Run 2 used the brief of the release, which lets the worker
show a claim through a caller of the function.
"""
from __future__ import annotations

import json
import sys
from datetime import datetime
from pathlib import Path

from bugs import WORK

HERE = Path(__file__).resolve().parent
RUNS = [("hpflow-import-live-run1", "first brief"), ("hpflow-import-live", "brief of the release")]
# The distinct bugs that the blind judge of `h2h` confirmed among the 12 findings (h2h/result.json, bug ids
# `covered_hint`, `k2`, `k12`), by the function and a word of the claim.
H2H_BUGS = {"covered_hint": ("unroutable_pin_hint", "id"), "k2": ("unroutable_pin_hint", "registry path"),
            "k12": ("_run_models_sync", "RuntimeError")}


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def one(name: str, what: str) -> dict:
    folder = WORK / name
    imports, verify, bugs = load(folder / "imports.json"), load(folder / "verify.json"), load(folder / "confirmed.json")
    records = [load(p) for p in sorted((folder / "records").glob("*.json"))]
    records = [r for r in records if r.get("run") in imports["runs"] + verify["runs"]]
    spans = [(datetime.fromisoformat(r["finished"]).timestamp() - (r.get("seconds") or 0), datetime.fromisoformat(r["finished"]).timestamp()) for r in records]
    found = {key: any(b["function"] == fn and word.lower() in b["claim"].lower() for b in bugs) for key, (fn, word) in H2H_BUGS.items()}
    return {"folder": name, "brief": what, "entries": len(imports["claims"]) + len(imports["skipped"]),
            "skipped": [s["reason"] for s in imports["skipped"]], "claims": len(imports["claims"]),
            "shown_by_a_repro": sum(1 for f in imports["findings"] if f["grade"] == 1),
            "not_shown": sum(1 for f in imports["findings"] if f.get("not_shown")),
            "import_sessions": len(imports["runs"]), "verifier_sessions": len(verify["runs"]),
            "confirmed_claims": sum(1 for c in verify["claims"] if c["class"] == "confirmed"),
            "confirmed_distinct_bugs": len(bugs),
            "bugs": [{"function": b["function"], "sources": b["sources"], "severity": b["severity"], "claim": b["claim"]} for b in bugs],
            "bugs_of_the_blind_judge_found": found,
            "cost_usd": round(sum(r.get("cost_usd") or 0 for r in records), 2),
            "wall_seconds": round(max(b for _, b in spans) - min(a for a, _ in spans))}


def main() -> int:
    h2h = load(HERE / "h2h" / "result.json")
    outside = [c for c in h2h["claims"] if c["arm"] != "hpf"]
    data = {"input": "the findings of Claude Code review and Codex review in h2h/findings_claude.json and h2h/findings_codex.json",
            "ref": "Puppetmaster v1.51.1",
            "blind_judge": {"findings": len(outside), "confirmed_claims": sum(1 for c in outside if c["confirmed"]),
                            "confirmed_distinct_bugs": len({c["bug"] for c in outside if c["confirmed"]})},
            "runs": [one(name, what) for name, what in RUNS if (WORK / name / "confirmed.json").exists()]}
    (HERE / "import_live.json").write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"blind_judge": data["blind_judge"],
                      "runs": [{k: r[k] for k in ("brief", "claims", "shown_by_a_repro", "not_shown", "confirmed_claims", "confirmed_distinct_bugs",
                                                  "bugs_of_the_blind_judge_found", "cost_usd", "wall_seconds")} for r in data["runs"]]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
