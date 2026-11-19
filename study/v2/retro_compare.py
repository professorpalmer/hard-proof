"""Compare the proof pipeline (retro/*.json) with the review arms (review_score.json) on the same bugs.

Run: python3 retro_compare.py            prints the summary and writes retro_compare.json
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent


def review_detections() -> tuple[dict[str, set], dict]:
    """The bugs that each review arm detected. The full score file has the text of each finding and is not in
    the public archive, so a slim copy (ids and costs only) is written beside it and read when the full file is absent."""
    full, slim = HERE / "review_score.json", HERE / "review_detected.json"
    if full.exists():
        data = json.loads(full.read_text())
        arms: dict[str, set] = {}
        for row in data["rows"]:
            if row["side"] != "pre":
                continue
            arm = f"{row['arm']}/{row['model']}"
            arms.setdefault(arm, set())
            if row.get("detected"):
                arms[arm].add(row["bug"])
        cost = {k: v["cost_usd"] for k, v in data["summary"].items()}
        slim.write_text(json.dumps({"detected": {k: sorted(v) for k, v in sorted(arms.items())}, "cost_usd": cost}, indent=1) + "\n", encoding="utf-8")
        return arms, cost
    data = json.loads(slim.read_text())
    return {k: set(v) for k, v in data["detected"].items()}, data["cost_usd"]


def main() -> int:
    retro = {p.stem: json.loads(p.read_text()) for p in sorted((HERE / "retro").glob("*.json"))}
    arms, review_cost = review_detections()
    ids = set(retro)
    proof = {b for b, r in retro.items() if str(r["outcome"]).startswith("detected")}
    scope = {b for b, r in retro.items() if (r.get("model") or {}).get("bug_in_model_scope")}
    out = {"bugs": len(ids), "proof_detected": len(proof), "in_scope": len(scope),
           "proof_detected_in_scope": len(proof & scope),
           "outcomes": dict(Counter(r["outcome"] for r in retro.values())),
           "outcomes_in_scope": dict(Counter(r["outcome"] for b, r in retro.items() if b in scope)),
           "cost_usd": round(sum(r.get("cost_usd") or 0 for r in retro.values()), 2),
           "seconds": sum(r.get("seconds") or 0 for r in retro.values()),
           "items": sum(len(r["items"]) for r in retro.values()),
           "items_not_the_bug": sum(1 for r in retro.values() for i in r["items"] if not i["hits_the_fix"]),
           "arms": {}}
    any_review = set()
    for arm, found in sorted(arms.items()):
        found = found & ids
        any_review |= found
        out["arms"][arm] = {"detected": len(found), "union_with_proof": len(found | proof),
                            "proof_only": len(proof - found), "review_only": len(found - proof),
                            "both": len(found & proof)}
    out["any_review_arm"] = len(any_review)
    out["union_all"] = len(any_review | proof)
    out["proof_only_vs_all_review"] = sorted(proof - any_review)
    out["proof_only_titles"] = {b: retro[b]["title"] for b in sorted(proof - any_review)}
    out["by_kind"] = {}
    for kind in sorted({r["kind"] for r in retro.values()}):
        k = {b for b, r in retro.items() if r["kind"] == kind}
        out["by_kind"][kind] = {"bugs": len(k), "proof": len(k & proof), "any_review": len(k & any_review)}
    costs = sorted(r.get("cost_usd") or 0 for r in retro.values())
    out["cost_median_usd"] = costs[len(costs) // 2] if costs else 0
    out["cost_mean_usd"] = round(sum(costs) / len(costs), 2) if costs else 0
    out["cost_range_usd"] = [costs[0], costs[-1]] if costs else []
    models = [r.get("model") or {} for r in retro.values()]
    out["model"] = {"made": sum(1 for r in retro.values() if r["outcome"] != "no model"),
                    "link_agrees_before_the_fix": sum(1 for m in models if m.get("link_pre") == "agree"),
                    "mutants_made": sum((m.get("mutants") or {}).get("made") or 0 for m in models),
                    "mutants_killed": sum((m.get("mutants") or {}).get("killed") or 0 for m in models),
                    "all_mutants_killed": sum(1 for m in models if (m.get("mutants") or {}).get("made") and not (m.get("mutants") or {}).get("survived"))}
    stage_cost: dict = {}
    for r in retro.values():
        for s in r["stages"]:
            name = "".join(ch for ch in s.get("stage", "?") if not ch.isdigit())
            stage_cost[name] = round(stage_cost.get(name, 0) + (s.get("cost_usd") or 0), 2)
    out["cost_by_stage_usd"] = stage_cost
    out["detected_at_step"] = dict(sorted(Counter(r["items"][-1]["step"] for b, r in retro.items() if b in proof and r["items"]).items()))
    out["items_by_kind"] = dict(Counter(i["kind"] for r in retro.values() for i in r["items"]))
    note = HERE / "retro_rerun_note.json"
    if note.exists():
        out["replaced_by_a_second_run"] = json.loads(note.read_text())["bugs_with_a_replaced_result"]
    out["review_cost_usd"] = review_cost
    (HERE / "retro_compare.json").write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
