#!/usr/bin/env python3
"""Hard Proof v2: three audits of one release range with different session settings.

Reads the stored audit folders of `hpf` (Puppetmaster v1.50.0..v1.51.1, 20 changed functions) and writes
`cost_cut.json`: sessions, cost and confirmed bugs for each setting, and which bugs each run found.

Run: python3 cost_cut.py
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from bugs import WORK

HERE = Path(__file__).resolve().parent
RUNS = [("audit-pm-1510", "First form: one session for each function, each worker with the settings of the user, two verifiers for each function with a finding"),
        ("audit-pm-1510-grouped", "One reviewer session for each file, the second verifier only where the first says real"),
        ("audit-pm-1510-lean", "Lean workers, one session for each function, the second verifier only where the first says real")]


def one(folder: str, label: str) -> dict:
    base = WORK / folder
    review = json.loads((base / "review.json").read_text())
    verify = json.loads((base / "verify.json").read_text())
    bugs = json.loads((base / "confirmed.json").read_text())
    rec = lambda i: json.loads((base / "records" / f"{i}.json").read_text())
    r_runs, v_runs = [rec(i) for i in review["runs"]], [rec(i) for i in verify["runs"]]
    by_model = Counter()
    for r in v_runs:
        by_model[r["model"]] += 1
    cost_r, cost_v = sum(r.get("cost_usd") or 0 for r in r_runs), sum(r.get("cost_usd") or 0 for r in v_runs)
    return {"folder": folder, "setting": label, "targets": len(json.loads((base / "targets.json").read_text())["targets"]),
            "review_sessions": len(r_runs), "verifier_sessions": len(v_runs), "verifier_sessions_by_model": dict(by_model),
            "review_cost_usd": round(cost_r, 2), "verify_cost_usd": round(cost_v, 2), "cost_usd": round(cost_r + cost_v, 2),
            "seconds": sum(r.get("seconds") or 0 for r in r_runs + v_runs),
            "findings_with_a_repro_that_runs": sum(1 for f in review["findings"] if f["grade"] >= 1),
            "classes": dict(Counter(c["class"] for c in verify["claims"])), "confirmed_bugs": len(bugs),
            "bugs": [{"file": b["file"], "function": b["function"]} for b in bugs]}


def main() -> int:
    out = {"range": "Puppetmaster v1.50.0..v1.51.1", "runs": [one(f, l) for f, l in RUNS]}
    (HERE / "cost_cut.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    for r in out["runs"]:
        print({k: r[k] for k in ("folder", "review_sessions", "verifier_sessions", "review_cost_usd", "verify_cost_usd", "cost_usd", "findings_with_a_repro_that_runs", "confirmed_bugs")})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
