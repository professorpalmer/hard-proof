#!/usr/bin/env python3
"""Hard Proof, experiment 13: a baseline with no proof duty.

Each task of this experiment is one decision point of an earlier experiment
where the proof worker did not know the answer: "is there a gap, or are the
laws complete?". The baseline worker gets the same model, laws and challenge
files, but it writes `answer.json` and no proof. No gate checks its answer.

Two arms:
  plain   no shell. The worker reads the files and reasons.
  tools   the worker can run `lake`, `lean` and `python3`.

The run folders have neutral names (a hash). They are outside this project,
so a worker cannot see the task name or the stored results near its folder.

Usage:
    python3 baseline.py build
    python3 baseline.py run --arm plain [--only ID,ID] [--concurrency 6]
    python3 baseline.py score
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RUNS = Path.home() / "Projects" / "hp-baseline"
MODELS = {"haiku": "claude-haiku-5-5", "sonnet": "claude-sonnet-5-5", "opus": "claude-opus-5-5"}
SKIP = re.compile(r"(^gate\d*\.py$|_gate\.py$|^comparator.*\.json$|_runs\.jsonl$|Solution\.lean$|^answer\.json$)")
KEEP_SOLUTION = {"Solution.lean", "SyncSolution.lean"}  # human-owned reference proofs of the main-table folders

FAMILY = {
    "tbl": {
        "context": "this Lean 4 project has a decision rule with boolean inputs. `Tbl.lean` has the model: a `Case` is one set of inputs, and a `Decide` is a rule that gives one answer for each case. `TblLaws.lean` has the laws for the rule. The owner believes that these laws describe the rule completely.",
        "gap": "Two rules each pass every law (`Tbl.Passes`), but they give different answers for one case.",
        "nogap": "Each two rules that pass every law give the same answer for each case.",
        "challenge": "`TblGapChallenge.lean` and `TblCompleteChallenge.lean`",
        "shape": '{"verdict": "gap" or "complete", "case": {"b0": true, "b1": false, ...}, "reason": "one or two sentences"}\n\nFor verdict "gap", `case` is one case for which two passing rules can give different answers. Give a value for each input of `Case`. For verdict "complete", leave `case` out.',
    },
    "recover": {
        "context": "this Lean 4 project models one rule of a real lock: when can a process remove a lock file that a different process left? `Recover.lean` has the model. A `Case` says what the recovery step knows. A `Decide` is a rule: it returns `true` when the lock file must be removed. `DESCRIPTION.md` has the sentences of the code's own documentation. `RecoverLaws.lean` has laws that an agent wrote from that description. The owner believes that these laws describe the rule completely.",
        "gap": "Two rules each pass every law (`Recover.Passes`), but they give different answers for one case.",
        "nogap": "Each two rules that pass every law give the same answer for each case.",
        "challenge": "`RecoverGapChallenge.lean` and `RecoverCompleteChallenge.lean`",
        "shape": None,
    },
    "sync12": {
        "context": "this Lean 4 project models a real command, `puppetmaster models sync`: it adds to a model registry the starter entries that the registry lacks. `Sync.lean` has the model. A `SyncImpl` is a design of the command: it takes the settings, the starter list and the registry, and returns the new registry. `DESCRIPTION.md` has the sentences of the command's own documentation. `SyncLaws.lean` has laws that an agent wrote from that description. The owner believes that these laws describe the command completely.",
        "gap": "Two designs each pass every law (`Sync.Passes`), but they give different registries for one legal input.",
        "nogap": "Each two designs that pass every law give the same registry for each legal input.",
        "challenge": "`SyncGapChallenge.lean` and `SyncCompleteChallenge.lean`",
        "shape": None,
    },
    "lock": {
        "context": "this Lean 4 project models a lock. `Laws.lean` defines the model and the laws. `Solution.lean` has a lock design `Exp.lock` and proofs that it obeys each law. The owner believes that the laws describe a correct lock completely.",
        "gap": "Two lock designs each pass every law (`Laws.Passes`), but after one sequence of events a process is in the critical section for one design and not for the other.",
        "nogap": "Each two lock designs that pass every law agree, after each sequence of events, on which process is in the critical section.",
        "challenge": "`GapChallenge.lean` and `CompleteChallenge.lean`",
        "shape": None,
    },
    "sync8": {
        "context": "this Lean 4 project models the command `puppetmaster models sync`. The command adds the starter models that a registry lacks. `SyncLaws.lean` defines the model and the laws. `refSync` is a model of the shipped code, and `SyncSolution.lean` proves that `refSync` obeys each law. The owner believes that the laws describe the command completely.",
        "gap": "Two sync designs each pass every law (`SyncLaws.Passes`), but they give different registries for one legal input.",
        "nogap": "Each two sync designs that pass every law give the same registry for each legal input.",
        "challenge": "`SyncGapChallenge.lean` and `SyncCompleteChallenge.lean`",
        "shape": None,
    },
}
FREE_SHAPE = ('{"verdict": "gap" or "complete", "open_decision": "one sentence: the decision that the laws leave open", '
              '"input": "the concrete legal input", "result_a": "the result of the first design", '
              '"result_b": "the result of the second design", "reason": "one or two sentences"}\n\n'
              'For verdict "complete", leave out `open_decision`, `input`, `result_a` and `result_b`.')
# Arm name -> (rule set, model override). The last three arms run only on the tasks that the plain arm got wrong.
ARMS = {"plain": ("plain", None), "tools": ("tools", None), "plain_repeat": ("plain", None), "plain_opus": ("plain", "opus")}
ARM_RULE = {
    "plain": "Do not run commands. Read the files and reason about them.",
    "tools": "You can run `lake`, `lean` and `python3` for analysis. If you write a script or a Lean file, put it in `.lake/` (git ignores that folder).",
}
ARM_TOOLS = {
    "plain": {"allowed_tools": ["Read", "Glob", "Grep", "Write", "Edit"],
              "disallowed_tools": ["Bash", "WebFetch", "WebSearch", "Task", "Agent", "NotebookEdit"]},
    "tools": {"allowed_tools": ["Bash(cd:*)", "Bash(ls:*)", "Bash(pwd)", "Bash(cat:*)", "Bash(git status:*)", "Bash(git diff:*)",
                                "Bash(git log:*)", "Bash(lake:*)", "Bash(lean:*)", "Bash(python3:*)", "Bash(shasum:*)",
                                "Bash(grep:*)", "Bash(wc:*)", "Bash(head:*)", "Bash(tail:*)", "Bash(sed -n:*)", "Bash(mkdir:*)"],
              "disallowed_tools": ["WebFetch", "WebSearch", "Task", "Agent"]},
}
CHECK = ("python3 -c \"import json; d = json.load(open('answer.json')); "
         "assert d.get('verdict') in ('gap', 'complete'), 'verdict must be gap or complete'\"")


def brief(family: str, arm: str) -> str:
    f = FAMILY[family]
    return (
        f"Context: {f['context']}\n\n"
        "Your role: you are the reviewer. Test that belief. One of two results is true, and you must find out which one:\n\n"
        f"1. A gap exists. {f['gap']}\n\n"
        f"2. No gap exists. {f['nogap']}\n\n"
        f"The challenge files ({f['challenge']}) state the two results exactly. You do not need to write a proof, and no proof checker reads your answer.\n\n"
        f"Your work: write the file `answer.json` in this folder. It is one JSON object with this shape:\n\n{f['shape'] or FREE_SHAPE}\n\n"
        f"Rules:\n- Write `answer.json` only. Do not change another file.\n- {ARM_RULE[arm]}\n"
        "- Stay in this folder. Do not read a file outside this folder.\n"
        "- Give your best answer. `verdict` must be \"gap\" or \"complete\".\n\n"
        "Report: say in plain words which result is true and why.")


def scrub(text: str) -> str:
    """Remove the text that tells which experiment a folder came from."""
    text = re.sub(r"experiment \d+[a-z]?", "experiment", text)
    text = re.sub(r"\s*Added after experiment[^\n]*\n[^\n]*-/", " -/", text)
    return text


def copy_files(src: Path, dst: Path, names: list[str] | None = None) -> None:
    dst.mkdir(parents=True, exist_ok=True)
    for path in sorted(src.iterdir()):
        if not path.is_file():
            continue
        if names is not None and path.name not in names:
            continue
        if SKIP.search(path.name) and path.name not in KEEP_SOLUTION:
            continue
        if path.suffix in (".lean", ".md", ".toml"):
            (dst / path.name).write_text(scrub(path.read_text(encoding="utf-8")), encoding="utf-8")
        else:
            shutil.copy(path, dst / path.name)
    (dst / ".gitignore").write_text(".lake/\n", encoding="utf-8")


def tasks() -> list[dict]:
    out = []
    for size in ("b06_l008", "b10_l032", "b14_l128", "b18_l512"):
        for truth in ("gap", "complete"):
            for model in MODELS:
                out.append({"family": "tbl", "source": f"exp11/{size}_{truth}", "truth": truth, "model": model,
                            "pair": f"reps/exp11b_{size}_{truth}.json", "label": f"table {size}"})
    for exp, family, pattern in (("exp10", "recover", "loop2_"), ("exp12", "sync12", "loop_"), ("exp12", "sync12", "loopb_")):
        for author in ("haiku", "sonnet", "opus"):
            result = json.loads((ROOT / exp / f"{pattern}{author}" / "result.json").read_text())
            for rnd in result["rounds"]:
                out.append({"family": family, "source": f"{exp}/{pattern}{author}/round{rnd['round']}_adversary",
                            "truth": rnd["mode"], "model": "sonnet", "pair": f"{exp}/{pattern}{author}/result.json",
                            "round": rnd["round"], "label": f"{exp} {pattern}{author} round {rnd['round']}",
                            "question": rnd.get("question")})
    for model in MODELS:
        out.append({"family": "lock", "source": "exp7/base", "laws_from": "exp6/base", "truth": "gap", "model": model,
                    "pair": "reps/exp6_gap.json", "label": "lock, three laws"})
        out.append({"family": "lock", "source": "exp7/base", "truth": "complete", "model": model,
                    "pair": "reps/exp7_complete.json", "label": "lock, four laws"})
        out.append({"family": "sync8", "source": "exp8/base_d", "laws_from": "exp8/base_c", "truth": "gap", "model": model,
                    "pair": "reps/exp8c_gap.json", "label": "sync, seven laws"})
        out.append({"family": "sync8", "source": "exp8/base_d", "truth": "complete", "model": model,
                    "pair": "reps/exp8d_complete.json", "label": "sync, eight laws"})
    for t in out:
        key = f"{t['source']}|{t.get('laws_from', '')}|{t['truth']}|{t['model']}"
        t["id"] = hashlib.sha256(("hp13|" + key).encode()).hexdigest()[:8]
    assert len({t["id"] for t in out}) == len(out)
    return out


def prepare(arm: str, t: dict) -> Path:
    """Make a new run folder for one task of one arm."""
    folder = RUNS / arm / t["id"]
    if folder.exists():
        shutil.rmtree(folder)
    copy_files(ROOT / t["source"], folder)
    if "laws_from" in t:
        # The gap variant of a main-table folder: the law file and its reference proofs of the smaller law set.
        names = ["Laws.lean", "Solution.lean"] if t["family"] == "lock" else ["SyncLaws.lean", "SyncSolution.lean", "SyncChallenge.lean"]
        copy_files(ROOT / t["laws_from"], folder, names)
    return folder


def build() -> int:
    todo = tasks()
    (HERE / "tasks.json").write_text(json.dumps(todo, indent=1) + "\n", encoding="utf-8")
    counts: dict[str, int] = {}
    for t in todo:
        counts[f"{t['family']} {t['truth']}"] = counts.get(f"{t['family']} {t['truth']}", 0) + 1
    print(json.dumps({"tasks": len(todo), "by_kind": counts}, indent=1))
    return 0


def sh(cmd: list[str], cwd: Path, timeout: int | None = None) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return proc.returncode, proc.stdout + proc.stderr


def parse_json(text: str) -> dict:
    return json.loads(text[text.find("{"): text.rfind("}") + 1])


def one_run(arm: str, t: dict) -> dict:
    rules, model = ARMS[arm]
    model = model or t["model"]
    folder = prepare(arm, t)
    sh(["git", "init", "-q"], folder)
    sh(["git", "add", "-A"], folder)
    sh(["git", "commit", "-q", "-m", "start"], folder)
    graph = {"id": f"hp13-{arm.replace('_', '-')}-{t['id']}", "entry": "answer",
             "defaults": {"adapter": "claude-code", "model": MODELS[model], "timeout_seconds": 1800, "finish": "criteria"},
             "nodes": [{"id": "answer", "kind": "agent", "role": "code", "files": ["answer.json"],
                        "task": brief(t["family"], rules), "payload": ARM_TOOLS[rules]},
                       {"id": "check", "kind": "shell", "command": CHECK},
                       {"id": "done", "kind": "end", "status": "pass"},
                       {"id": "failed", "kind": "end", "status": "fail"}],
             "edges": [{"from": "answer", "to": "check", "when": "ok"},
                       {"from": "check", "to": "done", "when": "ok"},
                       {"from": "check", "to": "answer", "when": "fail", "max": 1},
                       {"from": "check", "to": "failed", "when": "fail"},
                       {"from": "answer", "to": "failed"}]}
    gpath = folder / ".lake" / "graph.json"
    gpath.parent.mkdir(exist_ok=True)
    gpath.write_text(json.dumps(graph, indent=1), encoding="utf-8")
    result: dict = {"id": t["id"], "arm": arm, "model": model}
    _, out = sh(["puppetmaster", "flow", "run", str(gpath)], folder)
    try:
        run_id = parse_json(out)["run_id"]
    except Exception:
        result.update(error="launch", detail=out[-400:])
        return result
    result["flow"] = run_id
    _, out = sh(["puppetmaster", "flow", "wait", run_id, "--timeout", "2400"], folder, timeout=2700)
    try:
        flow = parse_json(out)
    except Exception:
        result.update(error="wait", detail=out[-400:])
        return result
    visits = [s for s in flow.get("steps", []) if s.get("node") == "answer"]
    seconds, cost, jobs = 0.0, 0.0, []
    for s in visits:
        for job in s.get("job_ids") or []:
            jobs.append(job)
            _, st = sh(["puppetmaster", "status", job], folder)
            try:
                j = json.loads(st)["job"]
                seconds += (datetime.fromisoformat(j["completed_at"]) - datetime.fromisoformat(j["created_at"])).total_seconds()
            except Exception:
                pass
            _, art = sh(["puppetmaster", "artifacts", job], folder)
            found = re.findall(r'total_cost_usd\\?":\s*([0-9.]+)', art)
            cost += float(found[-1]) if found else 0.0
    result.update(flow_status=flow.get("status"), visits=len(visits), jobs=jobs, seconds=round(seconds), cost_usd=round(cost, 3))
    try:
        result["answer"] = json.loads((folder / "answer.json").read_text(encoding="utf-8"))
    except Exception as exc:
        result["answer"] = None
        result["answer_error"] = str(exc)[:200]
    _, status = sh(["git", "status", "--short", "--untracked-files=all"], folder)
    result["changed_files"] = [l[3:] for l in status.splitlines() if l.strip()]
    return result


def run(arm: str, only: list[str], concurrency: int) -> int:
    todo = json.loads((HERE / "tasks.json").read_text())
    if only:
        todo = [t for t in todo if t["id"] in only]
    started = time.time()
    with ThreadPoolExecutor(max_workers=concurrency) as pool:
        results = list(pool.map(lambda t: one_run(arm, t), todo))
    path = HERE / f"results_{arm}.json"
    old = json.loads(path.read_text())["runs"] if path.exists() else []
    done = {r["id"] for r in results}
    merged = [r for r in old if r["id"] not in done] + results
    path.write_text(json.dumps({"arm": arm, "runs": merged}, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"arm": arm, "ran": len(results), "seconds": round(time.time() - started),
                      "cost_usd": round(sum(r.get("cost_usd") or 0 for r in results), 2),
                      "no_answer": [r["id"] for r in results if not r.get("answer")]}, indent=1))
    return 0


def in_removed_leaf(source: str, case: dict | None) -> bool | None:
    meta = json.loads((ROOT / "exp11" / "meta" / (Path(source).name + ".json")).read_text())
    leaf = meta.get("removed_leaf")
    if not leaf or not isinstance(case, dict):
        return None
    try:
        return all(bool(case[f"b{bit}"]) is bool(val) for bit, val in leaf["path"])
    except KeyError:
        return False


def proof_pair(t: dict) -> dict:
    """Time, cost and outcome of the proof worker at the same decision point."""
    data = json.loads((ROOT / t["pair"]).read_text())
    if "rounds" in data:
        rnd = next(r for r in data["rounds"] if r["round"] == t["round"])
        adv = rnd["adversary"]
        return {"proof_seconds": adv["seconds"], "proof_cost_usd": adv["cost_usd"], "proof_accept": rnd["pilot_gate"] == "accept", "proof_runs": 1}
    runs = [r for r in data["runs"] if r["model"] == t["model"]]
    if not runs:  # the Opus replicates of the main table are in a second record
        runs = json.loads((ROOT / t["pair"].replace(".json", "_opus.json")).read_text())["runs"]
    return {"proof_seconds": round(sum(r["worker_seconds"] for r in runs) / len(runs)),
            "proof_cost_usd": round(sum(r["cost_usd"] or 0 for r in runs) / len(runs), 3),
            "proof_accept": all(r["pilot_gate"] == "accept" for r in runs), "proof_runs": len(runs)}


def score() -> int:
    todo = {t["id"]: t for t in json.loads((HERE / "tasks.json").read_text())}
    judged = json.loads((HERE / "judgments.json").read_text()) if (HERE / "judgments.json").exists() else {}
    report: dict = {"arms": {}}
    for arm in ARMS:
        path = HERE / f"results_{arm}.json"
        if not path.exists():
            continue
        rows = []
        for r in json.loads(path.read_text())["runs"]:
            t = todo[r["id"]]
            said = (r.get("answer") or {}).get("verdict")
            row = {"id": r["id"], "family": t["family"], "label": t["label"], "model": r.get("model") or t["model"], "truth": t["truth"],
                   "said": said, "verdict_correct": said == t["truth"], "seconds": r.get("seconds"), "cost_usd": r.get("cost_usd"),
                   **proof_pair(t)}
            if t["truth"] == "gap" and said == "gap":
                if t["family"] == "tbl":
                    row["gap_valid"] = in_removed_leaf(t["source"], r["answer"].get("case"))
                    row["gap_check"] = "mechanical"
                else:
                    row["gap_valid"] = judged.get(f"{arm}/{r['id']}", {}).get("valid")
                    row["gap_check"] = "pilot reading"
                    row["gap_note"] = judged.get(f"{arm}/{r['id']}", {}).get("note")
            rows.append(row)
        summary: dict = {}
        for fam in sorted({x["family"] for x in rows}) + ["all"]:
            sel = [x for x in rows if fam == "all" or x["family"] == fam]
            gaps = [x for x in sel if x["truth"] == "gap"]
            comp = [x for x in sel if x["truth"] == "complete"]
            summary[fam] = {
                "runs": len(sel), "verdict_correct": sum(x["verdict_correct"] for x in sel),
                "gap_tasks": len(gaps), "gap_found": sum(x["said"] == "gap" for x in gaps),
                "gap_found_and_valid": sum(1 for x in gaps if x.get("gap_valid") is True),
                "gap_not_judged": sum(1 for x in gaps if x["said"] == "gap" and x.get("gap_valid") is None),
                "complete_tasks": len(comp), "false_gap": sum(x["said"] == "gap" for x in comp),
                "cost_usd": round(sum(x["cost_usd"] or 0 for x in sel), 2),
                "seconds": sum(x["seconds"] or 0 for x in sel),
                "proof_accept": sum(x["proof_accept"] for x in sel),
                "proof_cost_usd": round(sum(x["proof_cost_usd"] for x in sel), 2),
                "proof_seconds": sum(x["proof_seconds"] for x in sel),
            }
        report["arms"][arm] = {"summary": summary, "rows": rows}
    (HERE / "score.json").write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({a: v["summary"] for a, v in report["arms"].items()}, indent=1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["build", "run", "score"])
    parser.add_argument("--arm", choices=list(ARMS), default="plain")
    parser.add_argument("--only", default="")
    parser.add_argument("--concurrency", type=int, default=6)
    args = parser.parse_args()
    if args.command == "build":
        return build()
    if args.command == "run":
        return run(args.arm, [x for x in args.only.split(",") if x], args.concurrency)
    return score()


if __name__ == "__main__":
    sys.exit(main())
