"""Tests of the runner. Fake `claude`, `codex` and command tools on PATH write the files of a worker. No model call."""
from __future__ import annotations

import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from typing import Any, Dict, List

TOOL = Path(__file__).resolve().parent.parent
TESTS = Path(__file__).resolve().parent
for p in (TOOL, TESTS):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

from hpflow import adapters  # noqa: E402
from hpflow.cli import main  # noqa: E402
from hpflow.common import shell_python  # noqa: E402
from hpflow.direct import DirectRunner  # noqa: E402
from hpflow.runner import agent_graph  # noqa: E402
from test_hpflow import FlowCase, gone  # noqa: E402

FAKE_AGENT = r'''
import json, os, subprocess, sys, time, uuid
name = os.path.splitext(os.path.basename(sys.argv[0]))[0]
argv = sys.argv[1:]
if name == "codex" and argv[:2] == ["debug", "prompt-input"]:
    # The seed of the builtin skill bundle.
    system = os.path.join(os.environ["CODEX_HOME"], "skills", ".system")
    os.makedirs(system, exist_ok=True)
    open(os.path.join(system, ".codex-system-skills.marker"), "w").write("1")
    sys.exit(0)
prompt = sys.stdin.buffer.read().decode("utf-8")
with open(os.environ["FAKE_AGENT_LOG"], "a") as f:
    f.write(json.dumps({"exe": name, "argv": argv, "cwd": os.getcwd(), "prompt": prompt,
                        "codex_home": os.environ.get("CODEX_HOME")}) + "\n")
mode = os.environ.get("FAKE_AGENT_MODE", "")
if mode == "sleep":
    child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
    open(os.environ["FAKE_AGENT_PID"], "w").write(str(child.pid))
    time.sleep(60)
if name == "claude":
    resumed = "--resume" in argv
    session = argv[argv.index("--session-id") + 1]
elif name == "codex":
    resumed = argv[:2] == ["exec", "resume"]
    session = argv[2] if resumed else "thread-" + uuid.uuid4().hex[:8]
    if os.environ.get("FAKE_REFRESH"):
        open(os.path.join(os.environ["CODEX_HOME"], "auth.json"), "w").write('{"token": "refreshed"}')
else:
    # A command tool reads its task from the file named on its command line.
    assert open(argv[argv.index("--task") + 1], encoding="utf-8").read() == prompt
    resumed = False
if os.path.exists("claims.json"):
    claims = json.load(open("claims.json"))
    json.dump([{"k": c["k"], "verdict": "real", "duplicate_of": None, "what_goes_wrong": "add subtracts",
                "caller": "pkg/mod.py:1"} for c in claims], open("verdicts.json", "w"))
elif mode == "repair" and not resumed and "This is revision 2" not in prompt:
    open("findings.json", "w").write("not json")
else:
    json.dump([{"n": 1, "claim": "add subtracts", "expected": "5", "confidence": "high"}], open("findings.json", "w"))
    open("finding_1.py", "w").write("def run():\n    from pkg.mod import add\n    return repr(add(2, 3))\n")
message = "Wrote the report.\nVERDICT: PASS - report written"
if name == "claude":
    print(json.dumps({"type": "system", "subtype": "init", "session_id": session}))
    # A resumed session reports the cost of the session so far.
    print(json.dumps({"type": "result", "subtype": "success", "is_error": False, "result": message,
                      "session_id": session, "total_cost_usd": 0.5 if resumed else 0.4}))
elif name == "codex":
    if not resumed:
        print(json.dumps({"type": "thread.started", "thread_id": session}))
    print(json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": message}}))
    print(json.dumps({"type": "turn.completed", "usage": {"input_tokens": 100, "output_tokens": 10}}))
else:
    print(message)
'''

# The command line of a reviewer of hpflow 0.4.2 through Puppetmaster 1.52.0, from its dispatch receipt
# (2026-11-19, audit-pm-1510-tools), with the path of the executable, the session id and the settings file left out.
# One flag of that receipt is gone: `--exclude-dynamic-system-prompt-sections` (see `adapters.lean_args`).
RECEIPT_TAIL = [
    "--model", "claude-sonnet-5-5", "--permission-mode", "acceptEdits",
    "--allowedTools", "Read,Glob,Grep,Write,Edit," + ",".join(f"Bash({c}:*)" for c in adapters.SHELL_COMMANDS),
    "--disallowedTools", "WebFetch,WebSearch,Task,Agent,NotebookEdit",
    "--setting-sources", "", "--strict-mcp-config", "--tools", "Bash,Read,Grep,Glob,Write,Edit",
    "--effort", "medium"]


# The folders of `git` (and on Windows of `taskkill`), with no `puppetmaster` command.
if os.name == "nt":
    SYSTEM_PATH = [os.path.dirname(shutil.which("git") or "git"), os.path.join(os.environ.get("SYSTEMROOT", r"C:\Windows"), "System32")]
else:
    SYSTEM_PATH = ["/usr/bin", "/bin"]


def fake_tool(folder: Path, name: str) -> None:
    """A fake agent tool that each system can start: a `#!` file on POSIX, a `.cmd` file that runs Python on Windows."""
    if os.name == "nt":
        (folder / f"{name}.py").write_text(FAKE_AGENT, encoding="utf-8")
        (folder / f"{name}.cmd").write_text(f'@"{sys.executable}" "%~dp0{name}.py" %*\r\n', encoding="utf-8")
        return
    exe = folder / name
    exe.write_text("#!" + sys.executable + "\n" + FAKE_AGENT)
    exe.chmod(0o755)


class DirectCase(FlowCase):
    def setUp(self) -> None:
        super().setUp()
        root = Path(self._tmp.name)
        self.bin = root / "bin"
        self.bin.mkdir()
        for name in ("claude", "codex", "mytool"):
            fake_tool(self.bin, name)
        self.log = root / "agent.jsonl"
        self.codex_user = root / "codex-user"
        self.codex_user.mkdir()
        (self.codex_user / "auth.json").write_text('{"token": "first"}')
        (self.codex_user / "config.toml").write_text('model = "gpt-6.1-sol"\n\n[mcp_servers.big]\ncommand = "x"\n')
        keys = ("PATH", "FAKE_AGENT_LOG", "FAKE_AGENT_MODE", "FAKE_AGENT_PID", "FAKE_REFRESH", "CODEX_HOME",
                "HPFLOW_CODEX_HOME", "CLAUDE_CONFIG_DIR")
        self.saved = {k: os.environ.get(k) for k in keys}
        # No `puppetmaster` command on this PATH: hpflow must not need one.
        os.environ["PATH"] = os.pathsep.join([str(self.bin), *SYSTEM_PATH])
        os.environ["FAKE_AGENT_LOG"] = str(self.log)
        os.environ["CODEX_HOME"] = str(self.codex_user)
        os.environ["HPFLOW_CODEX_HOME"] = str(root / "codex-worker")
        os.environ["CLAUDE_CONFIG_DIR"] = str(root / "no-claude-config")
        for k in ("FAKE_AGENT_MODE", "FAKE_REFRESH"):
            os.environ.pop(k, None)

    def tearDown(self) -> None:
        for k, v in self.saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        super().tearDown()

    def direct(self, *args: str) -> tuple:
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main([*args, "--out", str(self.out)])
        return code, json.loads(buf.getvalue())

    def calls(self) -> List[Dict[str, Any]]:
        if not self.log.exists():
            return []
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def ready(self) -> None:
        self.init()
        self.assertEqual(self.direct("targets", "--changed", "HEAD~1..HEAD")[0], 0)

    def record(self) -> Dict[str, Any]:
        run = json.loads((self.out / "review.json").read_text())["runs"][0]
        return json.loads((self.out / "records" / f"{run}.json").read_text())


class DirectRunnerTest(DirectCase):
    def test_review_and_verify_on_claude_code(self):
        self.ready()
        code, r = self.direct("review", "--repro-timeout", "5")
        self.assertEqual((code, r["findings"], r["grade_1"]), (0, 1, 1), r)
        self.assertAlmostEqual(r["cost_usd_api_equivalent"], 0.4)
        call = self.calls()[0]
        argv = call["argv"]
        self.assertEqual(argv[:5], ["--print", "--output-format", "stream-json", "--verbose", "--session-id"])
        # The same arguments as Puppetmaster 1.52.0 gave the same worker.
        self.assertEqual(argv[6:], RECEIPT_TAIL)
        # The contract of a Puppetmaster flow: the gate preview, the build contract and the verdict line.
        self.assertIn("Done means: every acceptance criterion is met", call["prompt"])
        self.assertIn("Write scope: create, edit, or delete only paths that match these entries.", call["prompt"])
        self.assertIn("Command: " + shell_python("python3 -c"), call["prompt"])
        self.assertTrue(call["prompt"].rstrip().endswith("`VERDICT: PARTIAL - <what you could not finish or verify>`."))
        self.assertEqual(Path(call["cwd"]).parent, self.out / "runs")
        code, v = self.direct("verify")
        self.assertEqual((code, v["worker_runs"], v["confirmed_bugs"]), (0, 2, 1), v)
        models = [c["argv"][c["argv"].index("--model") + 1] for c in self.calls()[1:]]
        self.assertEqual(models, ["claude-sonnet-5-5", "claude-opus-5-5"])

    def test_a_failed_check_resumes_the_session_once(self):
        self.ready()
        os.environ["FAKE_AGENT_MODE"] = "repair"
        code, r = self.direct("review", "--repro-timeout", "5")
        self.assertEqual((code, r["grade_1"]), (0, 1), r)
        first, second = self.calls()
        self.assertNotIn("--resume", first["argv"])
        session = first["argv"][first["argv"].index("--session-id") + 1]
        i = second["argv"].index("--resume")
        self.assertEqual(second["argv"][i:i + 3], ["--resume", session, "--fork-session"])
        record = self.record()
        self.assertEqual([s["node"] for s in record["steps"]], ["work", "check", "work", "check"])
        self.assertEqual(record["steps"][0]["jobs"], [f"claude-code:{session}"])
        self.assertIn("Revision 2 of your task", second["prompt"])
        self.assertIn("JSONDecodeError", second["prompt"])
        # The resumed session reports its total: the node costs the largest value, the visit the difference.
        self.assertAlmostEqual(record["cost_usd"], 0.5)
        self.assertAlmostEqual(record["steps"][2]["cost_usd"], 0.1)

    def test_codex_review_with_a_repair_in_the_lean_home(self):
        self.ready()
        os.environ["FAKE_AGENT_MODE"] = "repair"
        os.environ["FAKE_REFRESH"] = "1"
        code, r = self.direct("review", "--repro-timeout", "5", "--adapter", "codex", "--model", "gpt-6.1-sol")
        self.assertEqual((code, r["adapter"], r["grade_1"]), (0, "codex", 1), r)
        self.assertIsNone(r["cost_usd_api_equivalent"])
        first, second = self.calls()
        self.assertEqual(first["exe"], "codex")
        home = Path(os.environ["HPFLOW_CODEX_HOME"])
        self.assertEqual(first["codex_home"], str(home))
        expected = ["exec", "--json", "-c", 'approval_policy="never"', "--sandbox", "workspace-write", "--skip-git-repo-check",
                    "-C", first["cwd"], "-m", "gpt-6.1-sol", *adapters.CODEX_NO_NET, "-c", "model_reasoning_effort=medium",
                    "--disable", "memories", "--disable", "multi_agent", "--", "-"]
        self.assertEqual(first["argv"], expected)
        thread = second["argv"][2]
        self.assertEqual(second["argv"][:2], ["exec", "resume"])
        self.assertTrue(thread.startswith("thread-"))
        self.assertIn('sandbox_mode="workspace-write"', second["argv"])
        self.assertNotIn("--sandbox", second["argv"])
        # The lean home: no MCP servers of the user, the builtin skills, and a refreshed login goes back to the user.
        self.assertNotIn("mcp_servers", (home / "config.toml").read_text())
        self.assertIn('model = "gpt-6.1-sol"', (home / "config.toml").read_text())
        self.assertTrue(list((home / "skills" / ".system").glob(".*marker")))
        self.assertEqual((self.codex_user / "auth.json").read_text(), '{"token": "refreshed"}')

    def test_codex_with_user_settings_runs_in_the_home_of_the_user(self):
        self.ready()
        code, r = self.direct("review", "--repro-timeout", "5", "--adapter", "codex", "--model", "gpt-6.1-sol",
                              "--user-settings")
        self.assertEqual(code, 0, r)
        call = self.calls()[0]
        self.assertEqual(call["codex_home"], str(self.codex_user))
        self.assertNotIn("multi_agent", call["argv"])

    def test_a_command_tool_and_a_repair_that_starts_it_again(self):
        self.ready()
        os.environ["FAKE_AGENT_MODE"] = "repair"
        code, r = self.direct("review", "--repro-timeout", "5", "--adapter", "command", "--model", "m1",
                              "--agent-cmd", "mytool --model {model} --cwd {folder} --task {prompt_file}")
        self.assertEqual((code, r["adapter"], r["grade_1"]), (0, "command", 1), r)
        first, second = self.calls()
        self.assertEqual(first["argv"][:4], ["--model", "m1", "--cwd", first["cwd"]])
        # A command tool has no session: the repair visit gets the full task and the feedback.
        self.assertIn("Your task:", second["prompt"])
        self.assertIn("This is revision 2; earlier work is already in the files.", second["prompt"])
        self.assertIn("JSONDecodeError", second["prompt"])
        self.assertIsNone(r["cost_usd_api_equivalent"])
        # A later command uses the stored template.
        code, v = self.direct("verify", "--models", "m1", "m2")
        self.assertEqual((code, v["adapter"], v["confirmed_bugs"]), (0, "command", 1), v)

    def test_a_timeout_ends_the_process_group(self):
        os.environ["FAKE_AGENT_MODE"] = "sleep"
        os.environ["FAKE_AGENT_PID"] = str(Path(self._tmp.name) / "pid")
        folder = Path(self._tmp.name) / "w"
        graph = agent_graph("hpf-1", "task", ["findings.json"], "claude-code", "claude-sonnet-5-5",
                            adapters.payload("claude-code"), check="true", timeout=2)
        r = DirectRunner(Path(self._tmp.name) / "graphs").run(graph, folder)
        self.assertEqual(r["status"], "failed", r)
        self.assertIn("timed out", r["steps"][0]["reason"])
        self.assertIsNone(r["cost_usd"])
        self.assertTrue(gone(int(Path(os.environ["FAKE_AGENT_PID"]).read_text())), "the child of the agent still runs")

    def test_a_missing_agent_command_is_an_error_record(self):
        self.ready()
        for f in self.bin.glob("claude*"):
            f.unlink()
        code, r = self.direct("review", "--repro-timeout", "5")
        self.assertEqual(code, 1, r)
        self.assertIn("not on PATH", json.dumps(self.record()))


if __name__ == "__main__":
    unittest.main()
