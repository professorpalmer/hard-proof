# hpflow: a proof gate and an audit ladder for Python code

This package has two commands.

- `hpf` is the audit ladder. It takes the Python functions that changed in a
  git range up a ladder of evidence: a review finding with a runnable repro,
  a script run of the repro, two verifier agents, a fix with a test, and a
  gate before the release. See the section "hpflow" below.
- `hp` is the proof gate. It is one proof gate for one Python function, with
  Lean 4. The first sections of this file are about `hp`.

The two come from the study "Proved is not finished"
(https://puppetmaster.gg/labs/hard-proof/). The study has the data, the costs
and the limits. Source: https://github.com/professorpalmer/hard-proof

`hp` replaces the hand-written gate scripts of the study
(`study/exp12/base/gate12.py` and the scripts before it) with one command set and
one domain contract. A new Python function gets a proof gate with no new gate
code.

The tool uses Lean 4.36.0 with no Mathlib. `lake comparator` does the
statement match, the axiom audit and the kernel replay. The tool is Python 3.9+
with the standard library only. It makes no model call.

## Install

```sh
pip install hpflow
```

This gives three commands: `hp` (the proof gate), and `hpf` and `hpflow` (the
audit ladder). The package has no Python dependency. From a checkout of the
repository, `./hp` and `./hpf` in the folder `tool` do the same with no
install.

The name of the package is `hpflow`. The name `hardproof` on PyPI is a
different project, and it is not related to these tools.

| Command | Needs |
| --- | --- |
| `hp` | Lean 4.36.0 through `elan`. No model call. |
| `hpf audit`, `hpf fix` | One agent command line with a login: Claude Code (the default), the Codex CLI, or any other agent tool through `--adapter command`. No orchestrator. These steps make model calls. |
| `hpf gate`, `hpf waive`, `hpf status` | git and Python only. No model call. |

## What the gate shows

A domain has a Lean mirror `ref` of the Python function and a set of laws
written from the documentation. The gate accepts certificates that untrusted
agents write:

- The link test shows that `ref` and the real function give the same output on
  many random legal inputs, and that the test kills mutants of the function.
- A `ref` certificate proves that `ref` passes each law.
- A `conflict` certificate proves that `ref` breaks one law on a legal input.
  The law or the code is wrong. A human decides.
- A `gap` certificate gives two designs that pass each law and differ on a
  legal input. The laws do not decide that input. A human decides.
- A `complete` certificate proves that two designs that pass each law agree on
  each legal input. Then the laws pin the behavior down.

## The domain contract

A domain is one folder for one function under test. The function has the type
`Impl := Input → Output` in Lean. A stateful system is out of scope; put the
state into `Input`.

Author files (an agent or a human writes them; then `pin` records them):

| File | Content |
| --- | --- |
| `hardproof.json` | `{"name": "...", "namespace": "HP", "python": {"module": "pkg.mod", "function": "name"}, "banned_in_laws": ["ref", ...]}` |
| `Types.lean` | namespace `HP`: `Input`, `Output` (each with `DecidableEq`), `abbrev Impl := Input → Output`, `def legal : Input → Bool`, `def Legal (x : Input) : Prop := legal x = true`, and the words that a law can use. No `ref` here. |
| `Ref.lean` | imports `Types`. `def HP.ref : HP.Impl`, the mirror of the Python code, and its helper functions. |
| `Codec.lean` | imports `Types`. `HP.decodeInput : String → Option Input`, `HP.encodeInput`, `HP.encodeOutput`, `HP.showInput`, `HP.showOutput`. One line of text for each value. |
| `link_adapter.py` | `gen(rng)`, `encode(case)`, `decode(line)`, `call(func, case)`, `encode_result(result)`, `is_legal(case)`. |
| `DESCRIPTION.md` | The sentences of the documentation, each an exact quote with its source file. Then a map from the model words to the documentation words. |
| `Laws.lean` | imports `Types` only. One `def <Name> (f : Impl) : Prop` for each law, `def Passes (f : Impl) : Prop` (the conjunction of all laws), and `theorem some_design_fails : ∃ f : Impl, ¬ Passes f`. |

Solution files (an untrusted agent writes them; the comparator checks them):

| File | Challenge statement |
| --- | --- |
| `RefPassesSolution.lean` | `theorem HPRef.ref_passes : Passes ref` |
| `ConflictSolution.lean` | first line `-- hardproof-law: <Law>`; `def HPConflict.input : Input`, `theorem HPConflict.input_legal : Legal input`, `theorem HPConflict.ref_breaks : ¬ <Law> ref` |
| `GapSolution.lean` | `def HPGap.designA`, `def HPGap.designB : Impl`, `def HPGap.input : Input`, `theorem HPGap.a_passes : Passes designA`, `theorem HPGap.b_passes : Passes designB`, `theorem HPGap.input_legal : Legal input`, `theorem HPGap.differ : designA input ≠ designB input` |
| `CompleteSolution.lean` | `theorem HPComplete.laws_complete : ∀ f g : Impl, Passes f → Passes g → ∀ x : Input, Legal x → f x = g x` |

Tool-owned files are in `hp/`: `lakefile.toml`, `lean-toolchain`,
`lake-manifest.json`, the challenge modules, the comparator configs,
`Runner.lean`, `QuestionGap.lean` and `QuestionConflict.lean`. The tool writes
them again before each check, so an edit to one of them has no effect. The
lakefile has one `lean_lib` for each solution, so a broken solution of one kind
does not stop the check of another kind.

## Quick start (on `examples/clamp`)

`examples/clamp` is a pure function `clamp(x, lo, hi)` in
`examples/clamp/pycode/clampmod.py`. It needs no outside repository. The examples are in the
repository, not in the installed package.

1. Copy the example to a new folder and go to it:

   ```sh
   cp -R examples/clamp /tmp/clamp-demo
   cd /tmp/clamp-demo
   ```

2. Set `HP` to the command: `HP=hp` after an install, or the full path of
   the launcher `hp` in the folder `tool` of a checkout.
3. Check the model (types, mirror, codec, runner and the codec round trip):

   ```sh
   $HP check model
   ```

4. Run the link test against the real function:

   ```sh
   $HP link --repo pycode --cases 5000
   ```

5. Check the laws and the `ref` certificate:

   ```sh
   $HP check laws ref
   ```

6. Pin the files, and check the pins:

   ```sh
   $HP pin
   $HP verify-pins
   $HP status
   ```

Each command prints one JSON report. The exit code is 0 for accept (or
`agree`), 1 for reject, and 2 for a usage error.

## Commands

All commands take `--dir PATH` (the domain folder; the default is the current
folder) and `--actor NAME` (the name in the run log). Run them as
`python3 -m hpflow.proof <command>` with `PYTHONPATH` set to this folder, or as
`./hp <command>`.

- `new DIR --name NAME --module PKG.MOD --function NAME`: make a domain folder
  with author stubs (each holds short instructions) and the tool-owned files.
- `generate`: write the tool-owned files again.
- `check model`: `Types`, `Ref`, `Codec` and `Runner` build. No `sorry`, no
  `axiom`, no `native_decide`, no `implemented_by`. The declarations have the
  types of the contract. The codec round trip holds on 200 cases from
  `link_adapter.gen`: `decode(encode(c)) == c`, and the Lean runner decodes
  each line.
- `link --repo PATH [--cases N] [--seed N] [--mutants N] [--function-file PATH]`:
  the link test. For each generated legal case, the Lean `ref` and the real
  function give the same output line. Then up to N mutants of the function
  source run on the same cases. The report gives the cases, the differences
  (must be 0), the first difference, the mutants made and killed, the kill
  rate, and each mutant that survives. The verdict is `agree` only when the
  differences are 0. The kill rate is reported, not judged. With
  `--function-file`, the function comes from that file and not from the module
  in `hardproof.json`.
- `check laws`: the text rules (imports `Types` only; no banned word of
  `hardproof.json` before `theorem some_design_fails`; no `sorry`, `axiom` or
  `native_decide`), the build, the types of `Passes` and `some_design_fails`,
  and the axiom audit (`propext`, `Quot.sound`, `Classical.choice` only). The
  report lists the law names.
- `check ref`, `check conflict`, `check gap`, `check complete`: build the
  solution, check that each required name exists, then run
  `lake comparator`. `--paranoid` runs the five extra kernels.
  `--inadvisably-no-sandbox` is added when `bwrap` is absent (macOS). For
  `conflict`, the named law must be a law of `Laws.lean`. You can name more
  than one kind; the check accepts when one kind is accepted.
- `question [gap|conflict]`: for an accepted gap, the encoded and shown input
  and the outputs of design A, design B and `ref`. For an accepted conflict,
  the law, the input and the output of `ref`.
- `pin`: write `hardproof.lock.json` with the SHA-256 of each author file and
  each generated file.
- `verify-pins [--expect FILE=SHA ...]`: reject when a pinned file differs.
  With `--expect`, check the given values (for example from a flow graph).
- `status`: what exists, and what the last check of each kind said.

Each `check` and each `link` appends one line to `hardproof_runs.jsonl` in the
domain folder: time, actor, command, verdict and seconds.

## The mutator

`link` mutates the source of the function with its own AST mutator. Each
mutant changes one place:

- negate the condition of an `if`, `while`, conditional expression or `assert`,
- swap `and` and `or`,
- change a comparison operator,
- change an integer constant by one,
- replace a `return` value by `None`,
- delete one statement,
- swap two positional arguments, or the values of two keyword arguments, of one call.

A mutant is killed when one case gives a different line, or when it raises or
runs for more than 30 seconds. The report also says if the unchanged source,
compiled the same way, agrees (`identity_copy_agrees`).

## Examples

- `examples/clamp`: `clamp(x, lo, hi)` over integers, with four laws and a
  `ref` certificate.
- `examples/sync`: `puppetmaster models sync` from experiment 12. `Input` holds
  the `--enable` flag, the locked adapters, the starter list and the registry.
  `Legal` is the corrected rule: the starter ids are pairwise distinct. The
  seven laws have no law for the order of the new rows, so `GapSolution.lean`
  shows a gap. `variants/order` adds an order law and a completeness proof.
  `variants/false_law` adds a false law and a conflict certificate. The link
  test needs a Puppetmaster clone:

  ```sh
  ./hp --dir examples/sync link --repo ~/Projects/hp-work/Puppetmaster
  ```

## Tests

```sh
python3 -m unittest discover tests
```

The tests make no model call. The Puppetmaster link test is skipped with a
message when the clone at `~/Projects/hp-work/Puppetmaster` is absent.

## hpflow

`hpflow` is the second package of this folder. It runs agent workers with the
agent command line that you have (Claude Code, Codex, or any other agent
tool) and takes a set of Python functions up an evidence ladder. It needs no
orchestrator. The proof gate `hp` makes no model call. `hpflow` does.

| Grade | Evidence | Who gives it |
| --- | --- | --- |
| 0 | A finding with a runnable repro | a reviewer agent |
| 1 | The repro runs on the source under audit and gives the result that the finding states | a script |
| 2 | Two verifier agents on different models each say `real`, and name a caller that reaches it | two agents |
| 3 | A fix with a regression test, a script check and an independent judge | agents and a script |

### Quick start

```sh
./hpf audit --repo . --ref HEAD --changed main..HEAD --out /tmp/audit
./hpf fix --out /tmp/audit
./hpf status --out /tmp/audit
```

Then read `/tmp/audit/REPORT.md` and the worktrees in `/tmp/audit/fix/`.

### What it needs

Python 3.9 or later, git, and one agent command line with a login. `hpflow`
starts that command itself in the folder of each worker.

- Claude Code (the default adapter, `npm install -g @anthropic-ai/claude-code`).
  A sign-in on the machine works. For a job with no browser, set
  `ANTHROPIC_API_KEY` (named in `claude --help`), or `CLAUDE_CODE_OAUTH_TOKEN`
  with a token from `claude setup-token` on a machine with a Claude
  subscription (the messages of the `claude` 2.1.316 binary name the two
  together).
- Codex (`--adapter codex`, `npm install -g @openai/codex`). A sign-in on the
  machine works. For a job with no browser, log in once:
  `printenv OPENAI_API_KEY | codex login --with-api-key`, or
  `printenv CODEX_ACCESS_TOKEN | codex login --with-access-token` (both from
  `codex login --help`, codex-cli 0.160.0).
- Any other agent tool (`--adapter command --agent-cmd "..."`, see below).

A CI job:

```sh
pip install hpflow
hpf audit --repo . --ref HEAD --changed "origin/main..HEAD" --out audit
hpf gate --out audit --ref HEAD
```

A bug that `REPORT.md` confirms makes `hpf gate` exit 1, so the job fails
until the bug is fixed or waived.

### Use another agent tool

With an adapter other than `claude-code`, give each model option: the
defaults are Claude Code models.

With Codex:

```sh
hpf audit --repo . --ref HEAD --changed v1.2.3..HEAD --out ~/audits/next \
  --adapter codex --model gpt-6.1-sol --models gpt-6.1-sol gpt-5.6-sol
hpf fix --out ~/audits/next --model gpt-6.1-sol --judge-model gpt-5.6-sol
```

The `fix` command has no `--adapter` here: it uses the adapter of the audit
folder (see the rule below).

With any other agent tool, give its command line as a template:

```sh
hpf audit --repo . --ref HEAD --changed v1.2.3..HEAD --out ~/audits/next \
  --adapter command --agent-cmd "mytool run --model {model} --cwd {folder} --task-file {prompt_file}" \
  --model big-model --models big-model other-model
```

The contract of a tool is short. It reads the task (the file `{prompt_file}`,
and the same text on its standard input), works in its current folder (also
`{folder}`), writes the files that the task names, prints its answer, and
ends the answer with the line `VERDICT: PASS - <reason>` (or `FAIL`,
`PARTIAL`). hpflow splits the template as a shell does and puts in the
values. No shell runs it, so a value cannot add a command. There is no second
template for a repair: a repair visit starts the tool again with the full
task and the feedback (the output of the failed check), as a Puppetmaster
flow did for a worker that it could not resume. So any tool works, also one
with no sessions. The cost of a command tool is unknown (`null`).

A provider with an API key bills each call. Plan billing of Codex or Claude
Code does not.

### Same workers as hpflow 0.4

Until 0.4, a Puppetmaster flow started the workers. 0.5 starts them itself,
with the arguments and the prompt text that Puppetmaster 1.52.0 gave them.
The source is the dispatch receipts of 0.4.2 audits (2026-11-19), and a test
compares the command line of a reviewer with such a receipt.

| What Puppetmaster gave a worker | 0.5 |
| --- | --- |
| Claude Code: `--print --output-format stream-json --verbose --session-id <id>`, the model, `--permission-mode acceptEdits` (a judge: `dontAsk` with `Edit`, `Write`, `NotebookEdit` disallowed), `--allowedTools`, `--disallowedTools`, the lean arguments of hpflow | kept |
| Claude Code: `--effort medium` | kept, as the option `--effort` (default `medium`) |
| Claude Code: `--settings ~/.claude/settings.json` (lean profile of 1.52.0, only when the file is a JSON object) | kept |
| Claude Code: a repair with `--resume <id> --fork-session --session-id <new id>` | kept |
| Codex: `codex exec --json -c approval_policy="never" --sandbox workspace-write --skip-git-repo-check -C <folder> -m <model>`, the no-network arguments, `-c model_reasoning_effort=medium`, and on a fresh start `--disable memories --disable multi_agent` | kept |
| Codex: a repair with `codex exec resume <thread>` and `-c sandbox_mode=...` | kept |
| Codex: a lean `CODEX_HOME` (the config of the user without MCP servers, plugins, hooks and memories; the global `AGENTS.md`; a copy of `auth.json` that goes back after a refresh; the builtin skills) | kept: `~/.hpflow/codex-worker-home` (`HPFLOW_CODEX_HOME` moves it). With the home of the user, the first request was 21,974 input tokens; with the lean home, 14,490 (codex-cli 0.160.0, one start each). `--user-settings` gives the home of the user |
| The prompt: the orientation line, the build contract with the `finish: criteria` text, the write scope, the task, the gate preview (the check command), the verdict line | kept, word for word, except one word: "Puppetmaster persists that report as a durable artifact" is now "hpflow stores that report with the run" |
| The prompt of a judge: the review contract and the judge verdict line | kept |
| A repair prompt: "Revision N of your task ..." with the output of the failed check | kept |
| CodeGraph context and memory in the prompt (`enrich_prompt_with_codegraph`, `prompt_with_memory`) | dropped: the run folders have no CodeGraph index and no memory, and the receipts show no such text |
| Environment `PUPPETMASTER_WORKER=1` and the job ids | dropped: no Puppetmaster to read them |

What a Puppetmaster flow had that hpflow does not have:

- The write-scope gate. Puppetmaster failed a worker that wrote outside the
  `files` of its node (`puppetmaster/gates.py`, `_gate_write_scope`). hpflow
  names the files in the prompt. What covers it: a reviewer and a verifier
  work on a copy (`runs/<id>/project/`), and the repro runs on the snapshot
  `src/`, so a stray write cannot change a grade. For a fix, the script check
  rejects a change outside the audit paths and the tests (`hpflow/fixcheck.py`),
  and the worker gets one visit to put it right.
- Durable resume of a flow. Puppetmaster saved a run after each step, and
  `flow resume` continued a run whose walker died (`docs/FLOWS.md`;
  `puppetmaster/flow.py`, `save_run`). What covers it: the record of each
  finished worker run. A later call does not repeat a stored run; a run that
  stopped in the middle runs again from its start.
- Retry of a transport failure (`flow.py`, `_execute_with_retries`). What
  covers it: a run with a launch error runs again on the next call; a failed
  run runs again with `--redo`.
- File claims between workers that write at one time (`docs/ADAPTERS.md`,
  "Universal runtime contracts"). What covers it: each worker has its own run
  folder or its own git worktree, so two workers never write the same files.
- The shared Codex host (one `codex app-server` for all Codex workers,
  `docs/FLOWS.md`, opt-in). Nothing covers it: each Codex worker starts its
  own `codex exec`. hpflow never turned the host on.
- The other adapters of Puppetmaster (`agentic`, `hermes`, `antigravity`,
  `fx`, `docs/ADAPTERS.md`). What covers it: `--adapter command` with the
  command line of that tool.
- The model registry check, routing, job receipts and the dashboard. Nothing
  covers it: the model goes to the command line of the tool as it is, and the
  tool reports a bad name. The logs of each run (prompt, command line,
  output) are in `direct/<run>/` of the audit folder.

### Use it as a gate before a release or a merge

The audit looks only at the functions that changed in a git range, so its cost
follows the size of the change. The gate is the last step. It makes no model
call, and its exit code is 0 for a pass and 1 for a fail.

```sh
hpf audit --repo . --ref HEAD --changed v1.2.3..HEAD --out ~/audits/next
hpf fix   --out ~/audits/next      # only when REPORT.md has confirmed bugs
# Review each worktree in ~/audits/next/fix/, then commit and merge the fixes yourself.
hpf gate  --out ~/audits/next --ref HEAD
```

`gate --ref REF` runs the repro of each confirmed bug on the commit `REF`. A
bug is closed when each of its repros gives a new result there. So the gate
checks the code that you will release, not the worktree of a fix worker. With
no `--ref`, a bug is closed when it has a fix with an accepted check and a
PASS judge.

When the owner decides that a confirmed bug stays as it is, record it:

```sh
hpf waive --out ~/audits/next --bug ID --reason "why the behavior stays" --by NAME
```

The gate fails when a review or a verifier run is absent, when a finding
came after the last `verify` and has no verdict, when a confirmed bug is
open, or when a repro does not run on `REF`. A range with no changed
function passes with no worker run.

What we measured on our two products (API-equivalent cost, Claude models):
about 0.47 US dollars for each changed function for the review and the
verifiers with the defaults of today (9.44 US dollars for 20 functions, 8 confirmed
bugs). The first form of the tool cost 28.53 US dollars for the same range and
confirmed 7 bugs: each worker loaded the settings of the user, and each
function with a finding had two verifier runs. One reviewer session for each
file (`--group file`) cost 8.94 US dollars and confirmed 3 bugs, so it is not the
default. On that audit, `gate --ref` failed on the audited release with 7
open bugs and passed on the next release with 7 closed.

### Findings of another reviewer

`hpf` can take the findings of another review tool, of a person, or of an
agent workflow. A finding of another tool has no repro, so it enters the
ladder as a claim. A worker must show each claim with a repro. A claim with a
repro that runs is a finding of grade 1, and the two verifiers and the gate
then handle it like a finding of the review step.

```sh
hpf audit --repo . --ref HEAD --findings other-review.json --out ~/audits/next
hpf gate  --out ~/audits/next --ref HEAD
```

With `--changed A..B` and `--findings FILE` in one call, the audit has the
two sources. On an audit folder that is there, `hpf import --findings FILE`
adds the claims, and `hpf verify` then judges them.

The findings file is a JSON list. Each entry names one function of a Python
file in the audited paths:

```json
[
  {"file": "pkg/mod.py", "function": "Class.method", "claim": "what is wrong"},
  {"file": "pkg/mod.py", "line": 120, "claim": "what is wrong", "source": "tool name"}
]
```

- `file`: the path in the repository. A full path below the repository is
  also read.
- `function` or `line`, or the two: the qualified name of the function, or a
  line inside it. A method name with no class name is read when the file has
  one such method.
- `claim`: the text of the finding.
- `source`: the name of the tool. `--source NAME` gives it for each entry
  that has none.

An object with the key `findings` is the same list. A SARIF 2.1.0 file is
also read: each result gives its message, the file and the start line of its
first location, and the name of its tool.

An entry that the ladder cannot take is skipped, and the report gives the
reason for each one: the place is not in a function, the file is not Python,
it is a test file, it is not in the audited paths, or the name fits two
functions. A file that is not JSON in one of these forms is a usage error.

The worker gives one answer for each claim: a repro, or a reason why it
cannot show the claim (`not_shown` in the report). A claim with no answer
makes the run a failed run, and the gate then fails. `REPORT.md` and
`confirmed.json` name the source of each claim.

What we measured (Claude models, `study/v2/import_live.json`): the 12
findings of two review tools on one release range of Puppetmaster, 10 from
Claude Code review and 2 from Codex review. One entry was about a test file
and was skipped. A worker showed 7 of the 11 claims with a repro and gave a
reason for the other 4 (style, speed, or behavior by design). The two
verifiers confirmed 4 claims, which are 3 distinct bugs. They are the 3 bugs
that a blind judge confirmed among the same 12 findings in an earlier test.
The run cost 2.19 US dollars and took 3.2 minutes.

A first run with an earlier brief found 2 of those 3 bugs. The third fault
shows only in a caller of the named function, and the worker said that the
function gives no wrong result. The brief now tells the worker to show such
a claim through the caller. This is the limit of the step: a claim that the
worker does not show does not reach a verifier. Read the `not_shown` list of
the report.

### Commands

All commands take `--out DIR` (the audit folder), `--redo`,
`--concurrency N` (default 5: the most workers that run at one time) and
`--user-settings`. A worker is lean by default. A Claude Code worker does not
load the Claude Code rules, MCP servers and personal skills of the user. That
start text was most of the cost of a worker run on our machine (about 83,000
tokens for each session). The lean arguments are `--setting-sources ""` and
`--strict-mcp-config`, `--settings` with the settings file of the user (so
the sign-in environment and the hooks stay), and since 0.5 a tool list:
`--tools Bash,Read,Grep,Glob,Write,Edit`. The schemas of all built-in tools
were about 25,000 tokens, and a worker reads them again on each turn: the
first request went from 33,500 to 8,800 tokens. On 95 known bugs a review
session then cost 26 percent less and found the same bugs (see "Limits" for
the numbers). An audit of 20 functions cost 5.38 US dollars against 8.25
with all tools (the mean of three audits against one), with 12 findings and
6 confirmed bugs against 13 and 8. A Codex worker runs in the lean Codex home. `--user-settings`
gives each worker the full profile of the user.

`review --short-prompt` (Claude Code only) also gives the reviewer a short
system prompt and one line that tells it to read less. A review then cost
about 25 percent less again, and it found fewer bugs in our test (see
"Limits"), so it is off by default.

`init` and `audit` take `--import-root DIR` for a repository whose top-level package is not at the
repository root: `--import-root src` for a `src/` layout, or the folder of the package in a larger
repository. A repro then imports the package with that folder first on the import path.

The commands that start workers (`review`, `import`, `verify`, `fix`, `audit`) also take
`--adapter claude-code|codex|command`, `--agent-cmd TEMPLATE` and
`--effort low|medium|high|xhigh` (default `medium`; not for `command`).

Each command that `hpflow` starts (an agent, a check, a repro, a test run,
git) runs in its own process group with a timeout. At the timeout the whole
group ends. Run them as `./hpf <command>` or as `python3 -m hpflow <command>`
with `PYTHONPATH` set to this folder. Each command prints one JSON report. The
exit code is 0 on success, 1 on a failed step, and 2 on a usage error.

All state is in the audit folder, as JSON files. A command can run again: it
does not repeat a worker run that has a stored result. `--redo` makes the
runs again. A stored run with a launch error runs again.

- `init --repo PATH --ref REF [--paths ...] [--python PATH] [--test-cmd "..."]`:
  write `audit.json` and the snapshot `src/` (`git archive` of the paths at
  the commit of `REF`). The default paths are each top-level folder with an
  `__init__.py`, and `tests`, `docs`, `README.md` and `pyproject.toml` when
  they are present. The default Python is `.venv/bin/python` of the
  repository, else the Python that runs `hpflow`. The test command is a
  template with `{python}` and `{tests}`; the default is
  `{python} -m pytest -q -p no:cacheprovider {tests}`.
- `targets (--changed A..B | --function FILE:NAME ... | --file FILE ...) [--max-lines 150] [--max N]`:
  write `targets.json`. `--changed` takes the functions and methods (from the
  `B` side) of non-test Python files that overlap a hunk of `git diff A..B`.
  The report lists the skipped functions with the reason: too long, test
  file, removed, or over `--max`.
- `review [--adapter NAME] [--model sonnet] [--shell | --no-shell] [--passes 1] [--repro-timeout 60] [--group file|function] [--group-size 6]`:
  one reviewer run for the changed functions of each file (at most
  `--group-size` functions in one run), and for each pass. `--group function`
  gives one run for each function. Each finding has a repro file
  `finding_<n>.py` with `run()`. A script runs each repro on `src/` in a
  separate process. A finding has grade 1 when `run()` returns. Else it stays
  at grade 0 with the reason (no repro file, an import error, a timeout, or
  an exception).
- `import --findings FILE ... [--source NAME] [--adapter NAME] [--model sonnet] [--repro-timeout 60]`:
  read the findings of another reviewer (see "Findings of another reviewer")
  and write `imports.json`. One worker run for the claims about each function
  (at most 8 claims in one run). The script that grades a review finding
  grades each repro. The files of the last call are the import of the audit
  folder. A stored worker result is used again.
- `verify [--adapter NAME] [--models sonnet opus] [--group file|function] [--all-verifiers]`:
  one verifier run for each file with grade-1 findings, from `review` and
  from `import`. The first model runs
  for each group. The other models run only for a group in which the first
  model says `real` for one claim or more, because a claim that the first
  verifier does not call `real` cannot be confirmed. `--all-verifiers` runs
  each model for each group. The default grouping is the grouping of the
  stored review. A finding has grade 2 when each verifier says `real`. Duplicates fold into one bug (the `duplicate_of` field of the
  first model). Writes `verify.json`, `confirmed.json` and `REPORT.md` (one
  table for each class: confirmed, real but not reachable, by design, mixed).
- `fix [--adapter NAME] [--base REF] [--only BUG ...] [--model opus] [--judge-model sonnet] [--rules TEXT]`:
  for each source file with confirmed bugs, a git worktree `fix/<slug>` on a
  new branch `hpfix/<slug>` from `--base` (default: the audited commit), in
  the audited repository. A build worker writes the fix and the test file
  `tests/test_hpfix_<slug>.py`. A script check (`python3 -m hpflow.fixcheck`)
  runs each repro (it must give a new result), the new test file and the
  related tests. A related test file of more than 400 KB is not run, and the
  report names it: such a file can run for a long time, and the CI of the
  repository runs it. A judge reviews the diff with a rubric. A failed check or a
  FAIL or PARTIAL review goes back to the builder. `hpflow` never commits,
  pushes or merges. The report lists each worktree, its diff stat, its new
  files, the check verdict and the judge verdict.
- `audit ...`: `init`, `targets`, `review` and `verify` in one call, with the
  options of each. It stops at the first step that fails. With
  `--findings FILE`, the call also has the `import` step, and it needs no
  targets: then it is `init`, `import` and `verify`.
- `status`: the adapter of the audit folder, the count of findings at each
  grade, the adapters, cost and time of each step, and what is not done.
- `waive --bug ID --reason TEXT [--by NAME]`: record in `waivers.json` that a
  confirmed bug stays as it is. A waiver needs a reason.
- `gate [--ref REF] [--repro-timeout 60]`: pass only when the audit is
  complete and each confirmed bug is closed or waived. The report lists each
  bug with its state and the reason. No model call.

Model names: on the `claude-code` adapter, `haiku`, `sonnet` and `opus` map to
`claude-haiku-5-5`, `claude-sonnet-5-5` and `claude-opus-5-5`. A full model id
passes through. On another adapter, a short Claude name is a usage error, and
each model option (`--model`, `--models`, `--judge-model`) must be given. The
model goes to the command line of the tool, which checks it. For a command
tool whose template has no `{model}`, the name is only a label (the two
verifiers need two labels).

The adapter rule: an `--adapter` option wins, and the command stores it as the
adapter of the audit folder (the key `adapter` of `audit.json`; `--agent-cmd`
goes to the key `agent_cmd`). A command with no `--adapter` uses the adapter
of the audit folder, else `claude-code`. So `verify`, `fix` and `status` after
`review --adapter codex` use Codex with no repeat of the option. A command
that stops on a usage error stores nothing. You can verify the findings of
one adapter with another: give `--adapter` to `verify`. The id of each stored
worker run has the adapter (and the template) when it is not `claude-code`,
and the effort when it is not `medium`. So the results of two adapters do not
mix, and the stored runs of hpflow 0.4 stay valid.

What each adapter gets (the file `hpflow/adapters.py` is the one table):

| Adapter | Write files in the run folder | Shell | No network | Lean start |
| --- | --- | --- | --- | --- |
| `claude-code` | `Read`, `Write`, `Edit`, `Glob`, `Grep` | `Bash` with a list of allowed commands; `--no-shell` removes it | `WebFetch`, `WebSearch`, `Task`, `Agent` are disallowed | `--settings`, `--setting-sources ""`, `--strict-mcp-config`, `--tools`, `--exclude-dynamic-system-prompt-sections` |
| `codex` | the `workspace-write` sandbox (a judge: `read-only`) | always: Codex reads files with its shell, so `--no-shell` is a usage error. No list of commands | `-c sandbox_workspace_write.network_access=false`, `-c web_search="disabled"` | the lean Codex home |
| `command` | what the tool does | what the tool does; `--no-shell` is a usage error | not set | not set |

The report of `review`, `verify` and `fix` has `adapter`, `effort` and
`adapter_notes`: what hpflow does not limit for that adapter.

Workers get a snapshot of the source, never the repository of the user. Each
run folder is `runs/<digits>`, and each worker gets a copy of `src/` as
`project/`. The name holds no word and no function name.

Cost is API-equivalent, as the agent tool reports it. Plan billing can apply.
`hpflow` reads the field `total_cost_usd`, and only Claude Code reports it.
For another adapter the cost is `null` (unknown), never 0. When some runs of
a step have no cost, the total is `null`, and the report adds
`cost_unknown_runs` and `cost_usd_of_the_other_runs`. A resumed Claude Code
session reports the cost of the session so far. So the cost of a node is the
largest value of its visits, and the cost of one visit is the difference from
the visit before it.

### Limits

- Grade 2 is the agreement of two agents. It is not a proof.
- A human owner of the code decides what is a bug, and reviews and commits
  each fix.
- Grade 1 shows only that the repro runs and gives a result. It does not show
  that the result is wrong.
- A pass of the gate says that each confirmed bug is closed or waived. It
  does not say that the code has no bug: in our study the best review arm
  found 44 of 95 known bugs.
- The fix step can make a wrong fix that passes its check and its judge (5 of
  45 in our study). Review each fix before you merge it.
- Python only.
- What we measured for 0.5 on 95 known bugs of our two products (a finding
  counts when its repro gives a different result before and after the fix,
  so no agent is the judge; the second number adds other findings whose
  result changed in a later release): the old worker arguments on 48 of the
  bugs, 17 and 33 for 7.24 US dollars; the defaults of 0.5 on the same 48, 18
  and 34 for 5.25; the defaults of 0.5 on all 95, 36 and 66. The runner of 0.5
  against Puppetmaster with one set of arguments on all 95: 36 and 60 against
  34 and 59 (58 in one of three score runs: one repro has no stable result). `--short-prompt` on all 95: 35 and 56, and 29 and 51
  in a second run. Haiku as the reviewer found 4 of 48, and a lower effort
  found 15 of 48 against 19, so neither is a default.
- One pass finds about a third of the known bugs, and each pass finds other
  ones: two passes with one set of arguments found 34 and 36, and 45 of 95
  together. `--passes 2` costs twice the
  review.
- Live runs of 0.5 with no Puppetmaster: `audit`, `fix` and `gate` on Claude
  Code (20 functions, 5 confirmed bugs, 5 accepted fixes, gate pass); `review`
  and `verify` on Codex; `review` and `verify` through `--adapter command`
  with opencode on OpenRouter (3 confirmed bugs on two functions). `fix` has
  no live run on Codex or on the `command` adapter.
- The audit of 0.5 on its own release (`hpf` on `hpflow-v0.4.2..HEAD`, then on
  each set of fixes): 7 rounds, 55 confirmed bugs, 52 closed by their repro
  and 3 with a waiver, 34.54 US dollars. The last round confirmed nothing.
  Confirmed bugs for each round: 23, 10, 7, 5, 6, 4, 0. A reviewer reads the
  whole function each time a line of it changes, so a round on fixes also
  finds older gaps. Three findings of the last round have no caller that
  reaches them and are open: an escape for a surrogate in a quoted key of the
  Codex configuration becomes a character, and a relative home folder of a
  repro is relative to the source tree.
- Windows: the tests of the ladder run there in CI. No live agent run was made
  on Windows. A child process that outlives its parent is not ended there.
- Lean certificates (the proof gate `hp`) are not part of the ladder. Use
  `hp` for a small rule that the owner states, for example a decision table.
