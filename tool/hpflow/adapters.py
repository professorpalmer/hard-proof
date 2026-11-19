"""The agent tools that hpflow starts, and the payload of each. This is the one place that knows how a tool limits a worker.

A worker of hpflow reads its task, works in its folder, writes the files of the task, and ends its answer with a
`VERDICT:` line. It can have a shell or not, and it has no network. The payload of a graph node holds the
settings of the tool; `hpflow.direct` turns them into a command line.

The texts and arguments copy what Puppetmaster 1.52.0 gave the same workers (the dispatch receipts of
hpflow 0.4.2 audits on 2026-11-19), so a worker of hpflow 0.5 starts as it did before.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence

from .common import UsageError

DEFAULT_ADAPTER = "claude-code"
COMMAND = "command"
ADAPTERS = ("claude-code", "codex", COMMAND)
EFFORTS = ("low", "medium", "high", "xhigh")
DEFAULT_EFFORT = "medium"
# The short model names of the default adapter. Another adapter takes a model name of its own tool.
CLAUDE_MODELS = {"haiku": "claude-haiku-5-5", "sonnet": "claude-sonnet-5-5", "opus": "claude-opus-5-5"}

# The shell commands of a reviewer and a verifier.
SHELL_COMMANDS = ("cd", "ls", "pwd", "cat", "git", "grep", "rg", "wc", "head", "tail", "sed", "awk", "sort", "uniq", "find",
                  "python3", "lake", "lean", "shasum", "mkdir", "cp", "mv", "diff", "echo", "test", "true")
# The shell commands of a fix worker and its judge: git only to read, and the python of the audit.
FIX_COMMANDS = ("cd", "ls", "pwd", "cat", "git diff", "git status", "git log", "git show", "git grep", "git blame", "grep",
                "rg", "wc", "head", "tail", "sed", "find", "python3", "sort", "uniq", "diff", "echo", "test", "mkdir", "timeout")

# Claude Code. A headless `acceptEdits` run refuses each shell command that has no allow rule, so the allow list
# is the shell limit.
CLAUDE_FILE_TOOLS = ["Read", "Glob", "Grep", "Write", "Edit"]
CLAUDE_NO_NET = ["WebFetch", "WebSearch", "Task", "Agent", "NotebookEdit"]
# A lean worker does not load the Claude Code rules, MCP servers and personal skills of the user. On a
# machine with large user rules, this start text was most of the cost of a worker run. The list does not
# have `--disable-slash-commands`: with it, the first request of each session was about 6,300 tokens larger.
LEAN_ARGS = ["--setting-sources", "", "--strict-mcp-config"]
# The schemas of all built-in tools were about 25,000 tokens of each request (33,500 with them, 8,800 with this
# list, Claude Code 2.1.316). A worker reads that text again on each turn, so it was most of the cost of a session.
LEAN_TOOLS = ["Read", "Grep", "Glob", "Write", "Edit"]

# Codex. The sandbox `workspace-write` limits the writes of each shell command to the folder. These two keys turn
# off the network of shell commands and the web search tool (both checked with codex-cli 0.160.0: a value of the
# wrong type is an error, so Codex knows the keys).
CODEX_NO_NET = ["-c", "sandbox_workspace_write.network_access=false", "-c", 'web_search="disabled"']


# `--short-prompt`: the system prompt of a reviewer on Claude Code, in place of the default one (about 3,000
# tokens less on each turn), with the read-less line of the brief. Measured on 95 known bugs (study,
# `v2/levers.py`): a review cost about 25 percent less. Two runs detected 35 and 29 bugs; two runs with the
# default prompt detected 34 and 36. The data does not show that detection holds, so this is not the default.
REVIEW_PROMPT = ("You are a careful software engineer who works in a terminal. Use the tools to read files, run commands and "
                 "write files. Do exactly what the task says. Keep your text short.")
# A line of the review brief for Claude Code: whole-file reads were a large part of the tokens that a session writes.
READ_LESS = ("The files of the project are large. Find the lines that you need with Grep, then read only those lines "
             "(Read with an offset and a limit). Do not read a whole file.\n\n")


def lean_args(shell: bool = True, reviewer: bool = False) -> List[str]:
    """The Claude Code arguments of a lean worker: no user settings, no MCP servers, and only the tools of the task.

    With `reviewer` (the option `--short-prompt` of the review step) the worker gets `REVIEW_PROMPT`.

    The list does not have `--exclude-dynamic-system-prompt-sections`. With that flag and the tool list, three
    audits of one range each gave 10 findings and 5 confirmed bugs. With the tool list alone, three audits gave
    11 to 13 findings and 5 to 7 confirmed bugs, and with neither, 13 findings and 8 confirmed bugs."""
    tools = (["Bash"] if shell else []) + LEAN_TOOLS
    return [*LEAN_ARGS, "--tools", ",".join(tools), *(["--system-prompt", REVIEW_PROMPT] if reviewer else [])]


def review_hint(adapter: str) -> str:
    """Text that the review brief of `adapter` gets after the arm text."""
    return READ_LESS if adapter == DEFAULT_ADAPTER else ""


def claude_settings_file() -> Optional[Path]:
    """The `settings.json` of the user, when it holds a JSON object.

    `--setting-sources ""` loads no settings file. `--settings <file>` gives back the environment block,
    the credential helpers, the permission rules and the hooks of the user, as Puppetmaster 1.52.0 does
    (`claude_user_settings_file`)."""
    root = os.environ.get("CLAUDE_CONFIG_DIR")
    path = (Path(root).expanduser() if root else Path.home() / ".claude").resolve() / "settings.json"
    try:
        # `utf-8-sig`: an editor on Windows can save the file with a byte order mark, and Claude Code reads such a file.
        return path if isinstance(json.loads(path.read_text(encoding="utf-8-sig")), dict) else None
    except (OSError, ValueError):
        return None


def claude_code(judge: bool, shell: bool, lean: bool, commands: Sequence[str], reviewer: bool = False) -> Dict[str, Any]:
    payload: Dict[str, Any] = {
        "allowed_tools": CLAUDE_FILE_TOOLS + ([f"Bash({c}:*)" for c in commands] if shell else []),
        "disallowed_tools": CLAUDE_NO_NET + ([] if shell else ["Bash"])}
    if lean:
        settings = claude_settings_file()
        payload["extra_args"] = (["--settings", str(settings)] if settings else []) + lean_args(shell, reviewer)
    return payload


def codex(judge: bool, shell: bool, lean: bool, commands: Sequence[str], reviewer: bool = False) -> Dict[str, Any]:
    if not shell:
        # Codex reads files with its shell. With `features.shell_tool=false` a worker has no tool that reads a file.
        raise UsageError("--no-shell is not possible with --adapter codex: Codex reads files with its shell tool, "
                         "and has no other read tool. Use the shell arm, or another adapter")
    # `lean_home`: the worker runs in a lean Codex home (hpflow.codexhome), as with Puppetmaster.
    return {"extra_args": list(CODEX_NO_NET), "lean_home": lean}


def command(judge: bool, shell: bool, lean: bool, commands: Sequence[str], reviewer: bool = False) -> Dict[str, Any]:
    if not shell:
        raise UsageError("--no-shell is not possible with --adapter command: hpflow cannot remove the shell of a tool "
                         "that it does not know")
    return {}


PAYLOADS: Dict[str, Callable[..., Dict[str, Any]]] = {
    "claude-code": claude_code, "codex": codex, COMMAND: command}

NOTES: Dict[str, List[str]] = {
    "claude-code": [],
    "codex": ["codex: the commands of the shell are not limited to a list. The workspace-write sandbox limits "
              "writes to the folder, and the network of shell commands and web search are off."],
    COMMAND: ["command: hpflow does not limit the tools, the shell commands or the network of this tool. "
              "A judge is not read-only. A repair visit starts the tool again with the full task and the feedback."],
}


def check(adapter: str, agent_cmd: Optional[str]) -> None:
    if adapter not in ADAPTERS:
        raise UsageError(f"no adapter {adapter}: use claude-code, codex, or command with --agent-cmd for any other agent tool")
    if adapter == COMMAND and not agent_cmd:
        raise UsageError("--adapter command needs --agent-cmd, for example "
                         "--agent-cmd 'mytool run --model {model} --cwd {folder} --task-file {prompt_file}'")


def payload(adapter: str, judge: bool = False, shell: bool = True, lean: bool = True,
            commands: Sequence[str] = SHELL_COMMANDS, effort: str = DEFAULT_EFFORT,
            agent_cmd: Optional[str] = None, reviewer: bool = False) -> Dict[str, Any]:
    """The payload of one worker or judge node. `reviewer`: the worker of the review step."""
    out = PAYLOADS[adapter](judge, shell, lean, commands, reviewer)
    if adapter == COMMAND:
        out["command"] = agent_cmd
    else:
        out["effort"] = effort
    return out


def notes(adapter: str, lean: bool = True) -> List[str]:
    """What hpflow does not limit for `adapter`, for the report of a command."""
    out = list(NOTES[adapter])
    if not lean and adapter == "codex":
        out.append("codex: --user-settings gives each worker the Codex home of the user, with its skills, MCP "
                   "servers and plugins.")
    if not lean and adapter == COMMAND:
        out.append("command: --user-settings has no effect.")
    return out


def model_id(adapter: str, name: str) -> str:
    """The model id of a worker. A short Claude name is valid only on the default adapter.

    Another name passes through to the command line of the tool, which checks it."""
    if name in CLAUDE_MODELS:
        if adapter != DEFAULT_ADAPTER:
            raise UsageError(f"`{name}` is a short Claude Code name, and the adapter is {adapter}. Give a model name "
                             f"that the {adapter} tool knows, for example the one in its own configuration")
        return CLAUDE_MODELS[name]
    return name


def model_or_default(adapter: str, given: Any, default: Any, option: str) -> Any:
    """The given model (or list of models), else the default of the default adapter.

    The defaults are Claude Code models, so another adapter needs the option. For a command tool whose
    template has no `{model}`, the name is only a label of the worker (the two verifiers need two labels)."""
    if given:
        return given
    if adapter == DEFAULT_ADAPTER:
        return default
    raise UsageError(f"give {option} for the adapter {adapter}: the default is a Claude Code model. "
                     f"Give a model name that the {adapter} tool knows")
