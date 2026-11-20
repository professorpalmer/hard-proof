"""The runner of hpflow: it starts the agent command line itself, in the folder of each worker.

`DirectRunner` walks the small graphs that hpflow builds (agent, judge, shell and end nodes; edges with
`when` ok, fail, PASS, FAIL or PARTIAL and `max`). Until hpflow 0.4 a Puppetmaster flow ran these graphs. The
runner keeps the contract of that flow, so the briefs need no change: the verdict lines (puppetmaster/flow.py,
`_JUDGE_VERDICT`, `_BUILD_VERDICT`), the revision text with the output of a failed check (`_revision_context`,
`_delta`), the gate preview (`_gate_preview`) and the build and review contracts of the CLI adapters
(puppetmaster/adapters/_prompts.py). The command lines copy the dispatch receipts of Puppetmaster 1.52.0.
"""
from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import sys
import threading
import time
import uuid
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from . import codexhome
from .adapters import COMMAND
from .common import (DEFAULT_CONCURRENCY, WINDOWS, UsageError, apply_cost_rule, lines_of, run_group, write_json,
                     write_python_shims)
from .runner import Runner

OUTPUT_CHARS = 6000
MAX_STEPS = 60
# The texts of puppetmaster/flow.py (`_JUDGE_VERDICT`, `_BUILD_VERDICT`) and puppetmaster/adapters/_prompts.py.
JUDGE_VERDICT = ("End your reply with exactly one line: `VERDICT: PASS - <summary>` or "
                 "`VERDICT: FAIL - <what is wrong, file:line>` or "
                 "`VERDICT: PARTIAL - <what could not be verified>`.")
BUILD_VERDICT = ("When you finish, end your reply with exactly one line: "
                 "`VERDICT: PASS - <what you built and checked>` or "
                 "`VERDICT: FAIL - <what still fails>` or "
                 "`VERDICT: PARTIAL - <what you could not finish or verify>`.")
ORIENTATION = ("Read this entire prompt before acting. Your assignment is the final section, the one headed "
               "\"Your task\". Everything above it -- output format, contract, repository context -- tells you HOW "
               "to answer and is never itself the thing to analyze, define, or ask about.")
FINISH = {
    "improve": "Passing checks are the floor, not the finish: when the task asks for quality the checks do not "
               "measure and time remains, improve it and run the checks again.",
    "criteria": "Done means: every acceptance criterion is met and every named check passes. When both are true, "
                "stop and write the report. Do not make more changes for quality that no criterion names."}
BUILD_CONTRACT = (
    "Build mode: you are a full-edit worker in this repository. Deliver working files, not a description of them: "
    "create and edit the files the task assigns you, and leave every other file alone; other workers own them.",
    "Work in a build-check loop: make the change, run the checks the task names (or the most relevant tests), "
    "read the results and fix what fails. {finish}",
    "Reporting contract: when you are done, end your final message with a short report \u2014 what you changed and "
    "why, the files you touched, and exactly what you ran to verify it. hpflow stores that report with the run; "
    "without it the run looks like it did nothing. Make the report's final line exactly one "
    "of `VERDICT: PASS - <what you did and checked>`, `VERDICT: FAIL - <what still fails>` or "
    "`VERDICT: PARTIAL - <what you did not finish>`; if you skipped any part of the task, the verdict is PARTIAL.",
    "Keep that report to a few lines and end it with exactly one line `VERDICT: PASS - reason` "
    "(or FAIL / PARTIAL). Do not return findings JSON.")
REVIEW_CONTRACT = (
    "Review mode: you are a read-only reviewer. Do not edit files. Inspect the work the task names: read the "
    "files and run read-only checks where they help.",
    "Report each problem on its own line as `path:line - what is wrong`, most important first. If you find "
    "none, say so plainly.",
    "End your reply with exactly one line: `VERDICT: PASS - <summary>` or `VERDICT: FAIL - <the most important "
    "problem>` or `VERDICT: PARTIAL - <what you could not verify>`. Do not return findings JSON.")
# The space of a verdict line is a space or a tab. Each other character is content (see `common.lines_of`).
VERDICT_LINE = re.compile(r"VERDICT:[ \t]*(PASS|FAIL|PARTIAL)[ \t]+[-–—][ \t]+(.*[^ \t])")
LEFT_OPEN = re.compile(r"\{\{[^{}]*\}\}")
SUCCESS_WHEN = ("always", "ok", "PASS")
# Claude Code: a judge runs as `--permission-mode dontAsk` and has no write tool (puppetmaster/adapters/claude_code.py,
# READ_ONLY_CLI_PERMISSION_MODE and READ_ONLY_DENIED_TOOLS).
CLAUDE_JUDGE_DENIED = ["Edit", "Write", "NotebookEdit"]
# Codex: a bounded worker in the lean home forks no subagents and keeps no memories (puppetmaster/adapters/codex.py).
CODEX_LEAN = ["--disable", "memories", "--disable", "multi_agent"]
STDIN_PROMPT = ["--", "-"]
PLACEHOLDERS = ("{model}", "{folder}", "{prompt_file}")


def parse_verdict(text: str) -> Optional[Tuple[str, str]]:
    """The one terminal `VERDICT` line, as `parse_terminal_verdict` of Puppetmaster reads it."""
    # Only a space, a tab and a carriage return are space around a line. Another character is content.
    lines = [line.strip(" \t\r") for line in lines_of(text or "") if line.strip(" \t\r")]
    found = [line for line in lines if line.startswith("VERDICT:")]
    if len(found) != 1 or found[0] != lines[-1]:
        return None
    m = VERDICT_LINE.fullmatch(found[0])
    return (m.group(1), m.group(2)) if m else None


def edge_matches(when: str, ok: bool, verdict: Optional[str]) -> bool:
    if when == "always":
        return True
    if when == "ok":
        return ok
    if when == "fail":
        return not ok
    # A run that failed has no verdict to trust, even when its text ends in one.
    return ok and verdict == when


def gate_preview(graph: Dict[str, Any], node: Dict[str, Any]) -> str:
    """The shell checks and judge tasks that follow a build node on its success edges."""
    nodes = {n["id"]: n for n in graph["nodes"]}
    steps: List[str] = []
    seen, current = {node["id"]}, node["id"]
    while True:
        nxt = next((e["to"] for e in graph["edges"] if e["from"] == current and e.get("when", "always") in SUCCESS_WHEN
                    and e["to"] not in seen), None)
        target = nodes.get(nxt) if nxt else None
        if target is None or target["kind"] not in ("shell", "judge"):
            break
        seen.add(nxt)
        if target["kind"] == "shell":
            steps.append(f"Command: {LEFT_OPEN.sub('(output of the steps above)', target['command'])}")
        else:
            steps.append("Review:\n" + LEFT_OPEN.sub("(output of the steps above)", target["task"]))
        current = nxt
    if not steps:
        return ""
    listed = "\n\n".join(f"{i}. {step}" for i, step in enumerate(steps, 1))
    return ("After you finish, your result goes through these steps in this order:\n\n"
            f"{listed}\n\nRun the commands yourself and check your result against the review "
            "before you finish. Do not write the review.")


def first_prompt(graph: Dict[str, Any], node: Dict[str, Any], prev: str, visit: int) -> str:
    """The prompt of a fresh session: the flow text of the node inside the contract of a CLI adapter."""
    task = node["task"]
    if node["kind"] == "judge":
        return "\n".join([ORIENTATION, "", *REVIEW_CONTRACT, "", "Your task:", f"{task}\n\n{JUDGE_VERDICT}"])
    if visit > 1:
        feedback = prev.strip() or "(the previous step gave no details)"
        task += f"\n\nThis is revision {visit}; earlier work is already in the files. Feedback to act on:\n{feedback}"
    preview = gate_preview(graph, node)
    if preview:
        task += f"\n\n{preview}"
    task += f"\n\n{BUILD_VERDICT}"
    finish = "criteria" if (node.get("finish") or (graph.get("defaults") or {}).get("finish")) == "criteria" else "improve"
    scope = [str(f) for f in node.get("files") or []]
    scope_lines = (["Write scope: create, edit, or delete only paths that match these entries. "
                    "A change outside them fails the task.", *(f"- {f}" for f in scope), ""] if scope else [])
    contract = [line.format(finish=FINISH[finish]) for line in BUILD_CONTRACT]
    return "\n".join([ORIENTATION, "", *contract, "", *scope_lines, "Your task:", task])


def resume_prompt(node: Dict[str, Any], prev: str, visit: int) -> str:
    """The prompt of a resumed session: only what changed (as `_delta` of the flow)."""
    if node["kind"] == "judge":
        return ("The work changed since your last review. Review it again against the same task: confirm the "
                f"problems you flagged are fixed and look for regressions.\n\n{node['task']}\n\n{JUDGE_VERDICT}")
    feedback = prev.strip() or "(the previous step gave no details)"
    return (f"Revision {visit} of your task. Your earlier work in this session is already on disk.\n\n"
            f"Feedback to act on:\n{feedback}\n\nFix what the feedback asks, rerun the checks, and finish.\n\n{BUILD_VERDICT}")


def claude_command(exe: str, model: Optional[str], payload: Dict[str, Any], judge: bool,
                   session: Optional[str], new_session: str) -> List[str]:
    """`claude --print` as `build_claude_code_command` of Puppetmaster builds it. The prompt goes on stdin.

    A repair resumes the session as a fork with its own id, so each visit has its own session."""
    cmd = [exe, "--print", "--output-format", "stream-json", "--verbose"]
    if session:
        cmd += ["--resume", session, "--fork-session"]
    cmd += ["--session-id", new_session]
    if model:
        cmd += ["--model", model]
    cmd += ["--permission-mode", "dontAsk" if judge else "acceptEdits"]
    allowed = payload.get("allowed_tools")
    denied = list(payload.get("disallowed_tools") or [])
    if judge:
        denied = list(dict.fromkeys(denied + CLAUDE_JUDGE_DENIED))
    if allowed:
        cmd += ["--allowedTools", ",".join(allowed)]
    if denied:
        cmd += ["--disallowedTools", ",".join(denied)]
    cmd += [str(a) for a in payload.get("extra_args") or []]
    return cmd + (["--effort", payload["effort"]] if payload.get("effort") else [])


def codex_command(exe: str, model: Optional[str], payload: Dict[str, Any], judge: bool, folder: Path,
                  session: Optional[str], lean_home: bool) -> List[str]:
    """`codex exec` and `codex exec resume` as `build_codex_exec_command` and `build_codex_resume_command` build them."""
    sandbox = "read-only" if judge else "workspace-write"
    if session:
        # `exec resume` takes no `--sandbox` and no `-C`: the sandbox is a `-c` value, the folder is the cwd.
        cmd = [exe, "exec", "resume", session, "--json", "-c", 'approval_policy="never"', "-c", f'sandbox_mode="{sandbox}"',
               "--skip-git-repo-check"]
    else:
        cmd = [exe, "exec", "--json", "-c", 'approval_policy="never"', "--sandbox", sandbox, "--skip-git-repo-check",
               "-C", str(folder)]
    if model:
        cmd += ["-m", model]
    cmd += [str(a) for a in payload.get("extra_args") or []]
    if payload.get("effort"):
        cmd += ["-c", f"model_reasoning_effort={payload['effort']}"]
    return cmd + (CODEX_LEAN if lean_home and not session else []) + STDIN_PROMPT


def template_command(template: str, model: Optional[str], folder: Path, prompt_file: Path) -> List[str]:
    """The command of `--adapter command`: the template split as a shell would split it, with the placeholders
    `{model}`, `{folder}` and `{prompt_file}` put in. No shell runs it, so a value cannot add a command."""
    out = []
    for token in shlex.split(template):
        for key, value in (("{model}", model or ""), ("{folder}", str(folder)), ("{prompt_file}", str(prompt_file))):
            token = token.replace(key, value)
        out.append(token)
    return out


def check_template(template: str) -> None:
    try:
        parts = shlex.split(template)
    except ValueError as e:
        raise UsageError(f"--agent-cmd is not a valid command line: {e}")
    if not parts:
        raise UsageError("--agent-cmd is empty")


def json_lines(text: str) -> List[Dict[str, Any]]:
    out = []
    # Only a newline ends an event: splitlines would also cut a JSON string at a raw U+2028 or \x0c.
    for line in text.split("\n"):
        line = line.strip()
        if line.startswith("{"):
            try:
                value = json.loads(line)
            except ValueError:
                continue
            if isinstance(value, dict):
                out.append(value)
    return out


def read_claude(stdout: str) -> Dict[str, Any]:
    """The final message, the session and the cost of a `stream-json` run."""
    events = json_lines(stdout)
    result = next((e for e in reversed(events) if e.get("type") == "result"), None)
    session = (result or {}).get("session_id") or next((e.get("session_id") for e in events if e.get("session_id")), None)
    cost = (result or {}).get("total_cost_usd")
    return {"done": result is not None and not result.get("is_error"), "message": str((result or {}).get("result") or ""),
            "session": session, "cost": float(cost) if isinstance(cost, (int, float)) and not isinstance(cost, bool) else None}


def read_command(stdout: str) -> Dict[str, Any]:
    """The answer of a command tool is its standard output. It reports no session and no cost."""
    return {"done": True, "message": stdout[-OUTPUT_CHARS * 4:], "session": None, "cost": None}


def read_codex(stdout: str) -> Dict[str, Any]:
    """The final message, the thread and the tokens of a `--json` run. Codex reports no cost."""
    events = json_lines(stdout)
    thread = next((e.get("thread_id") for e in events if e.get("type") == "thread.started"), None)
    messages = [str((e.get("item") or {}).get("text") or "") for e in events
                if e.get("type") == "item.completed" and (e.get("item") or {}).get("type") == "agent_message"]
    turn = next((e for e in reversed(events) if e.get("type") == "turn.completed"), None)
    return {"done": turn is not None, "message": messages[-1] if messages else "", "session": thread, "cost": None,
            "tokens": (turn or {}).get("usage")}


class DirectRunner(Runner):
    """Runs a graph of hpflow. The record has the shape that a Puppetmaster flow gave hpflow 0.4."""

    name = "direct"

    def __init__(self, graph_dir: Path, concurrency: int = DEFAULT_CONCURRENCY):
        self.graph_dir = graph_dir
        self.concurrency = max(1, concurrency)
        # At most this many graphs run at one time, whatever the number of threads that call `run`.
        self.slots = threading.BoundedSemaphore(self.concurrency)

    def run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        with self.slots:
            return self._run(graph, folder)

    @staticmethod
    def executable(graph: Dict[str, Any]) -> Optional[str]:
        adapter = graph["defaults"]["adapter"]
        if adapter == COMMAND:
            node = next(n for n in graph["nodes"] if n["kind"] in ("agent", "judge"))
            return shutil.which(shlex.split(node["payload"]["command"])[0])
        return shutil.which("claude" if adapter == "claude-code" else "codex")

    def _run(self, graph: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        folder.mkdir(parents=True, exist_ok=True)
        self.graph_dir.mkdir(parents=True, exist_ok=True)
        gpath = self.graph_dir / f"{graph['id']}.json"
        write_json(gpath, graph)
        flow = f"direct-{uuid.uuid4().hex[:12]}"
        logs = self.graph_dir.parent / "direct" / flow
        record: Dict[str, Any] = {"graph": str(gpath), "flow": flow, "runner": self.name, "logs": str(logs)}
        adapter = graph["defaults"]["adapter"]
        exe = self.executable(graph)
        if exe is None:
            record.update(status="error", error="launch", detail=f"the command of the adapter {adapter} is not on PATH")
            return record
        nodes = {n["id"]: n for n in graph["nodes"]}
        visits: Dict[str, int] = {}
        edge_counts: Dict[int, int] = {}
        sessions: Dict[str, str] = {}
        steps: List[Dict[str, Any]] = []
        current, prev, status = graph["entry"], "", "stuck"
        for _ in range(MAX_STEPS):
            node = nodes[current]
            if node["kind"] == "end":
                status = "done" if node.get("status", "pass") == "pass" else "failed"
                break
            visits[current] = visits.get(current, 0) + 1
            visit = visits[current]
            if node["kind"] == "shell":
                item = self._shell(node, folder)
            else:
                item = self._agent(graph, node, folder, exe, adapter, prev, visit, sessions, logs)
            item["node"] = current
            steps.append(item)
            prev = item.pop("output", "")
            nxt = self._next(graph, node, item, edge_counts)
            if nxt in ("done", "failed", "stuck"):
                status = nxt
                break
            current = nxt
        nodes_cost = apply_cost_rule(steps)
        record.update(status=status, steps=steps, jobs=[j for s in steps for j in s.get("jobs") or []],
                      node_cost_usd=nodes_cost,
                      cost_usd=None if nodes_cost is None else round(sum(nodes_cost.values()), 4),
                      seconds=sum(s.get("seconds") or 0 for s in steps))
        return record

    @staticmethod
    def _next(graph: Dict[str, Any], node: Dict[str, Any], item: Dict[str, Any], counts: Dict[int, int]) -> str:
        """The next node, as `_pick_edge` of the flow chooses it."""
        if node["kind"] == "judge" and item["ok"] and item["verdict"] is None:
            item["reason"] = f'no-edge: judge "{node["id"]}" gave no verdict'
            return "stuck"
        outgoing = [(i, e) for i, e in enumerate(graph["edges"]) if e["from"] == node["id"]]
        if not outgoing:
            return "done" if item["ok"] else "failed"
        exhausted = False
        for i, e in outgoing:
            if not edge_matches(e.get("when", "always"), item["ok"], item["verdict"]):
                continue
            # A used up edge gives way to a later matching edge, such as the fallback to "failed".
            if e.get("max") is not None and counts.get(i, 0) >= e["max"]:
                exhausted = True
                continue
            counts[i] = counts.get(i, 0) + 1
            return e["to"]
        if exhausted:
            return "stuck"
        return "failed" if not item["ok"] else "stuck"

    @staticmethod
    def _shell(node: Dict[str, Any], folder: Path) -> Dict[str, Any]:
        start = time.monotonic()
        timeout = float(node.get("timeoutMs", 600000)) / 1000.0
        code, out, err = run_group(node["command"], folder, timeout, shell=True)
        output = (out + err)[-OUTPUT_CHARS:]
        verdict = parse_verdict(output)
        reason = f"timed out after {timeout:.0f}s" if code is None else ("" if code == 0 else f"exit {code}")
        return {"ok": code == 0, "verdict": verdict[0] if verdict else None, "reason": reason[:400], "jobs": [],
                "seconds": round(time.monotonic() - start), "output": output}

    def _agent(self, graph: Dict[str, Any], node: Dict[str, Any], folder: Path, exe: str, adapter: str, prev: str,
               visit: int, sessions: Dict[str, str], logs: Path) -> Dict[str, Any]:
        defaults = graph.get("defaults") or {}
        judge = node["kind"] == "judge"
        payload = node.get("payload") or {}
        model = node.get("model") or defaults.get("model")
        timeout = float(node.get("timeout_seconds") or defaults.get("timeout_seconds") or 3600)
        session = sessions.get(node["id"])
        prompt = resume_prompt(node, prev, visit) if session else first_prompt(graph, node, prev, visit)
        logs.mkdir(parents=True, exist_ok=True)
        stem = f"{node['id']}-{visit}"
        prompt_file = logs / f"{stem}.prompt.txt"
        prompt_file.write_bytes(prompt.encode("utf-8"))
        env = dict(os.environ)
        python = defaults.get("python")
        if python and python != sys.executable:
            # The briefs say `python3`, and the allow lists name `python3`. The shim folder first on PATH makes that
            # name the Python of the project, so a worker can import the dependencies of the project. With the
            # Python of hpflow as the project Python, the worker keeps the `python3` of the machine, as before 0.6.1.
            shims = write_python_shims(self.graph_dir.parent / "bin", python)
            env["PATH"] = str(shims) + os.pathsep + env.get("PATH", "")
        home = None
        if adapter == "claude-code":
            cmd = claude_command(exe, model, payload, judge, session, str(uuid.uuid4()))
        elif adapter == "codex":
            home = codexhome.prepare(exe) if payload.get("lean_home") else None
            if home is not None:
                env["CODEX_HOME"] = str(home)
            cmd = codex_command(exe, model, payload, judge, folder, session, home is not None)
        else:
            cmd = template_command(payload["command"], model, folder, prompt_file)
            if WINDOWS:
                # Windows starts a bare name only as `name.exe`. `shutil.which` also finds `name.cmd` (PATHEXT).
                cmd[0] = exe
        start = time.monotonic()
        code, out, err = run_group(cmd, folder, timeout, env=env, stdin=prompt)
        seconds = round(time.monotonic() - start)
        if home is not None:
            codexhome.sync_back(home)
        (logs / f"{stem}.stdout.txt").write_text(out, encoding="utf-8")
        (logs / f"{stem}.stderr.txt").write_text(err, encoding="utf-8")
        write_json(logs / f"{stem}.argv.json", cmd)
        got = {"claude-code": read_claude, "codex": read_codex}.get(adapter, read_command)(out)
        if got["session"]:
            sessions[node["id"]] = got["session"]
        ok = code == 0 and got["done"]
        verdict = parse_verdict(got["message"])
        if code is None:
            reason = f"timed out after {timeout:.0f}s"
        elif not ok:
            reason = f"exit {code}: {(err or got['message'])[-300:]}"
        else:
            reason = verdict[1] if verdict else ""
        item: Dict[str, Any] = {"ok": ok, "verdict": verdict[0] if verdict else None, "reason": reason[:400],
                                "jobs": [f"{adapter}:{got['session']}"] if got["session"] else [],
                                "seconds": seconds, "reported_usd": got["cost"], "resumed": session is not None,
                                "output": got["message"][-OUTPUT_CHARS:]}
        if got.get("tokens"):
            item["tokens"] = got["tokens"]
        return item
