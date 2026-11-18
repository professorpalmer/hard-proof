#!/usr/bin/env python3
"""Hard Proof v2, experiment 17: the proof loop as ONE Puppetmaster flow.

The adversary and the law author are each one worker session. A later round resumes
the session of the worker and gives it only the change. Experiment 12 started a new
worker in a new folder for each round. Same law sets, same model, same gate.

Usage:
    python3 durable_loop.py --start a_haiku --base base --name dl_a_haiku
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
from pathlib import Path

from flowrun import job_record, parse_json, sh

HERE = Path(__file__).resolve().parent
EXP12 = HERE.parent / "exp12"
WORK = Path.home() / "Projects" / "hp-work" / "dl"
STEP = HERE / "dl_step.py"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", required=True)
    parser.add_argument("--base", default="base")
    parser.add_argument("--name", required=True)
    parser.add_argument("--model", default="claude-sonnet-5-5")
    parser.add_argument("--max-rounds", type=int, default=8)
    args = parser.parse_args()
    os.environ["HP_BASE"] = args.base
    sys.path.insert(0, str(EXP12))
    import loop12  # noqa: E402

    base = EXP12 / args.base
    rid = hashlib.sha256(f"hp17|{args.name}".encode()).hexdigest()[:10]
    folder = WORK / rid
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir(parents=True)
    for f in loop12.HUMAN + [".gitignore", "lake-manifest.json"]:
        shutil.copy(base / f, folder / f)
    with (folder / ".gitignore").open("a") as fh:
        fh.write("\nROUND.md\n")
    laws = (EXP12 / args.start / "SyncLaws.lean").read_text(encoding="utf-8")
    (folder / "SyncLaws.lean").write_text(laws, encoding="utf-8")
    state_path = WORK / f"{rid}.state.json"
    state_path.write_text(json.dumps({
        "pins": {f: hashlib.sha256((folder / f).read_bytes()).hexdigest() for f in loop12.HUMAN},
        "laws_sha": hashlib.sha256(laws.encode("utf-8")).hexdigest(), "laws_before": laws, "rounds": []}, indent=1))
    env = f"HP_BASE={args.base}"
    gate = f"{env} {sys.executable} {STEP} gate {state_path}"
    lawgate = f"{env} {sys.executable} {STEP} lawgate {state_path}"
    law_task = (
        "Context: this Lean 4 project models a real command, `puppetmaster models sync`. `SyncLaws.lean` has the laws for this command. An adversary proved that the laws leave one behavior open. The file `ROUND.md` has the open case and the answer of the owner.\n\n"
        "Your work: add to `SyncLaws.lean` the law that this answer shows was absent. Write a general law for the requirement behind the answer, not a law for this one input only. Then add the new law to `Passes`, and keep `ref_passes` and `some_design_fails` proved.\n\n"
        "The gate is `python3 gate12.py check laws`. It prints a JSON report. Verdict `accept` is the only success.\n\n"
        "Rules:\n- Edit `SyncLaws.lean` only.\n- Do not change or remove a law that is in the file. Add to the file.\n- The new law must be true for the shipped code (`ref`). It says what a user of the command can observe. It must not mention `ref` or `adjust`, and it must not copy their code.\n- Do not add a law that the answer does not support.\n- Do not use `sorry`, a new `axiom`, or `native_decide`.\n- The toolchain is Lean 4.36.0 with no Mathlib.\n\n"
        "Report: the new law in plain words.")
    tools = {"allowed_tools": loop12.TOOLS}
    graph = {
        "id": f"hp17-{rid}", "entry": "adversary",
        "defaults": {"adapter": "claude-code", "model": args.model, "timeout_seconds": 3000, "finish": "criteria", "preview": False},
        "nodes": [
            {"id": "adversary", "kind": "agent", "role": "code", "files": ["SyncGapSolution.lean", "SyncCompleteSolution.lean"],
             "task": loop12.ADVERSARY_TASK, "payload": tools,
             "revise": "Your work continues. This is what happened since your last result:\n\n{{prev}}\n\nIf the gate rejected your result, correct it. If the laws changed, `SyncLaws.lean` has one more law now and your old solution files were removed: decide again for the laws as they are now, and write a gap certificate or a completeness proof. The gate command is the same."},
            {"id": "gate", "kind": "shell", "command": gate},
            {"id": "law", "kind": "agent", "role": "code", "files": ["SyncLaws.lean"], "task": law_task, "payload": tools,
             "revise": "Your work continues. This is what happened since your last result:\n\n{{prev}}\n\nIf the gate rejected the laws, correct them. If `ROUND.md` has a new open case, add the law for that case in the same way as before."},
            {"id": "lawgate", "kind": "shell", "command": lawgate},
            {"id": "done", "kind": "end", "status": "pass"},
            {"id": "failed", "kind": "end", "status": "fail"}],
        "edges": [
            {"from": "adversary", "to": "gate", "when": "ok"},
            {"from": "gate", "to": "done", "when": "out~=RESULT_COMPLETE"},
            {"from": "gate", "to": "law", "when": "out~=RESULT_GAP"},
            {"from": "gate", "to": "adversary", "when": "fail", "max": 4},
            {"from": "gate", "to": "failed"},
            {"from": "law", "to": "lawgate", "when": "ok"},
            {"from": "lawgate", "to": "adversary", "when": "ok", "max": args.max_rounds},
            {"from": "lawgate", "to": "law", "when": "fail", "max": 4},
            {"from": "lawgate", "to": "failed"},
            {"from": "adversary", "to": "failed"},
            {"from": "law", "to": "failed"}]}
    sh(["git", "init", "-q"], folder)
    sh(["git", "add", "-A"], folder)
    sh(["git", "-c", "user.name=hp", "-c", "user.email=hp@localhost", "commit", "-q", "-m", "start"], folder)
    gpath = WORK / f"{rid}.graph.json"
    gpath.write_text(json.dumps(graph, indent=1), encoding="utf-8")
    result: dict = {"name": args.name, "start": args.start, "base": args.base, "folder": rid}
    _, out = sh(["puppetmaster", "flow", "run", str(gpath)], folder)
    try:
        run_id = parse_json(out)["run_id"]
    except Exception:
        result.update(error="launch", detail=out[-800:])
        print(json.dumps(result, indent=1))
        return 1
    _, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", "7200"], folder, timeout=7500)
    flow = parse_json(out)
    steps = []
    for s in flow.get("steps", []):
        item = {"node": s.get("node"), "verdict": s.get("verdict"), "ok": s.get("ok")}
        if s.get("job_ids"):
            secs, cost = 0.0, 0.0
            for j in s["job_ids"]:
                a, b = job_record(j, folder)
                secs += a
                cost += b
            item.update(seconds=round(secs), cost_usd=round(cost, 3), jobs=s["job_ids"])
        steps.append(item)
    state = json.loads(state_path.read_text())
    _, out = sh([sys.executable, "gate12.py", "check", "gap", "complete", "--paranoid", "--actor", "pilot-verify"], folder)
    try:
        final = parse_json(out)
    except Exception:
        final = {}
    # The cost that Claude Code reports for a resumed session is the total of the session so far.
    # The cost of one visit is the difference from the visit before it of the same node.
    last: dict = {}
    for s in steps:
        if "cost_usd" in s:
            s["session_cost_usd"] = s["cost_usd"]
            s["cost_usd"] = round(s["session_cost_usd"] - last.get(s["node"], 0.0), 3)
            last[s["node"]] = s["session_cost_usd"]
    agent_steps = [s for s in steps if "cost_usd" in s]
    result.update(flow=run_id, flow_status=flow.get("status"), steps=steps,
                  questions=sum(1 for r in state["rounds"] if r["mode"] == "gap"),
                  rounds=state["rounds"], pilot_gate=final.get("verdict"), pilot_gate_mode=final.get("accepted_mode"),
                  worker_sessions=len({s["node"] for s in agent_steps}), worker_visits=len(agent_steps),
                  cost_usd=round(sum(s["cost_usd"] for s in agent_steps), 2), seconds=sum(s["seconds"] for s in agent_steps),
                  final_laws=loop12.law_names((folder / "SyncLaws.lean").read_text(encoding="utf-8")))
    out_dir = HERE / "durable"
    out_dir.mkdir(exist_ok=True)
    (out_dir / f"{args.name}.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({k: result.get(k) for k in ("name", "flow_status", "questions", "pilot_gate_mode", "worker_visits", "cost_usd", "seconds")}
                     | {"visits": [(s["node"], s.get("cost_usd"), s.get("seconds")) for s in agent_steps]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
