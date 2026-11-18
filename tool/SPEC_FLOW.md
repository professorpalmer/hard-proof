# hpflow: the audit ladder as one command set

Status: specification. Owner of this file: the pilot.

## Purpose

`hardproof` (this folder) checks certificates and makes no model call. `hpflow` is the second
package of this folder. It runs agent workers through the Puppetmaster command line and takes a
set of Python functions up an evidence ladder:

| Grade | Evidence | Who gives it |
| --- | --- | --- |
| 0 | A finding with a runnable repro | a reviewer agent |
| 1 | The repro runs on the source under audit and gives the result that the finding states | a script |
| 2 | Two verifier agents on different models each say `real`, and name a caller that reaches it | two agents |
| 3 | A fix with a regression test, a script check and an independent judge | agents and a script |

(Grades with Lean certificates come later and use `hardproof`.)

The working versions of each step exist as study scripts. Use them as the reference for the briefs,
the checks and the flow graphs, and keep the brief texts unless this file says otherwise:
`~/Projects/hard-proof/v2/flowrun.py` (start one flow, collect cost and time),
`review.py` (reviewer brief, repro run, scoring), `audit_findings.py` (verifier brief, merge),
`fix.py` and `fix_check.py` (fix worker, check, judge graph), `bugs.py` (`run_snippet`, `comparable`).
Read them with `cat`. Do not change them. The study scripts depend on a data set of historical bugs;
`hpflow` must not: its input is a repository and a list of functions.

## Rules for the code

- Python 3.9+, stdlib only, `from __future__ import annotations`, no emojis, JSON not YAML.
- Package `hpflow/` in this folder, launcher script `./hpf` (same form as `./hp`). `python3 -m hpflow <command>`.
- All prose in short plain sentences. No contractions.
- Each command prints one JSON report to stdout. Exit 0 on success, 1 on a failed step, 2 on a usage error.
- All state is in one audit folder (`--out DIR`), as JSON files. Each command can run again and
  continues: it does not repeat a worker run that has a stored result (`--redo` forces it).
- Worker runs go through a `Runner` class with one method that takes a flow graph and a folder and
  returns a record (status, steps, job ids, cost, seconds). `PuppetmasterRunner` calls
  `puppetmaster flow run` and `puppetmaster flow wait` as `flowrun.py` does. Tests use a `FakeRunner`
  that writes the files that a worker would write. No test makes a model call.
- Cost rule: the provider tool reports the cost of a resumed session as the total of the session so
  far. The cost of a node is the largest value of its visits, and the cost of one visit is the
  difference from the visit before it. Report cost as "API-equivalent" and say that plan billing can apply.
- Run folders of workers have a hash for a name (no word such as test, eval, bug, or the name of a
  function in the path), below `DIR/runs/`.
- Workers get a source snapshot, never the repository of the user: `git archive <ref>` of the
  configured paths into `DIR/src`, copied into each run folder as `project/` (use `cp -Rc` on macOS when available).
- Model names are parameters. Defaults: review `sonnet`, verify `opus` and `sonnet`, fix `opus`,
  judge `sonnet` (map: haiku `claude-haiku-5-5`, sonnet `claude-sonnet-5-5`, opus `claude-opus-5-5`; a full model id passes through).
  Adapter `claude-code`. `--concurrency N` (default 8).

## Commands

- `init --repo PATH --ref REF --out DIR [--paths pkg tests docs ...] [--python PATH] [--test-cmd "..."]`:
  write `DIR/audit.json` (repo, ref resolved to a commit, package paths, the Python that runs the tests,
  the test command template) and the snapshot `DIR/src`. Default paths: each top-level folder that has an
  `__init__.py`, plus `tests`, `docs`, `README.md`, `pyproject.toml` when present.
- `targets (--changed A..B | --function FILE:NAME ... | --file FILE ...) [--max-lines 150] [--max N]`:
  write `DIR/targets.json`. `--changed`: the functions and methods (AST of the `B` side) in non-test
  Python files of the package paths whose lines overlap a diff hunk of `git diff A..B`. Report also the
  functions that were skipped and why (too long, test file, removed).
- `review [--model M] [--shell | --no-shell] [--passes N]`: one reviewer run for each target and pass
  (brief of `review.py`, at most 5 findings, each with `finding_<n>.py` that defines `run()`). Then the
  script gate: run each repro on `DIR/src` in a separate process with a timeout (as `run_snippet`). A
  finding passes grade 1 when `run()` returns. Store the result text. A finding whose repro cannot
  import the function or times out stays at grade 0 with the reason.
- `verify [--models M1 M2]`: group the grade-1 findings by target, one verifier run for each group and
  model (brief of `audit_findings.py`), merge. A finding has grade 2 when each verifier says `real`.
  Fold duplicates into one bug (the `duplicate_of` field of the first model). Write `DIR/confirmed.json`
  and `DIR/REPORT.md` (a table for each verdict class: confirmed, real but not reachable, by design, mixed).
- `fix [--base REF] [--only BUG ...]`: for each source file with confirmed bugs, a git worktree
  `DIR/fix/<slug>` on a new branch `hpfix/<slug>` cut from `--base` (default: the audited ref), in the
  repository of the audit. Then the graph of `fix.py`: build worker, script check (each repro gives a new
  result, the new test file passes, related tests pass), judge with the rubric; a FAIL or PARTIAL review
  goes back to the builder (limits as in `fix.py`). Never commit, push or merge. The report lists each
  worktree, its diff stat, the check verdict and the judge verdict.
- `audit ...`: `init`, `targets`, `review`, `verify` in one call, with the options of each.
- `status`: counts for each grade, cost and time for each step, and what is not done.

## Tests (the acceptance for this work)

`python3 -m unittest discover tests` must pass with the existing `hardproof` tests. New tests, with no model call:
1. `targets --changed` on a small git repository that the test makes in a temp folder: a changed function
   is found, a changed test file is not, a function that is too long is reported as skipped.
2. `review` with a `FakeRunner` that writes findings and repro files: a repro that returns gets grade 1,
   a repro that raises `ImportError` or times out stays at grade 0.
3. `verify` with a `FakeRunner`: two `real` verdicts give grade 2, a mixed pair does not, duplicates fold.
4. `fix` with a `FakeRunner`: the worktree and the branch exist, the report has the diff stat, and
   the repository has no new commit.
5. A second call of each command makes no new worker run. `--redo` makes them again.
6. The cost rule: a node with visits that report 0.4 and 0.5 costs 0.5, and its second visit costs 0.1.
7. Run folder names have no banned word.

Add a section "hpflow" to `README.md`: the ladder table, a quick start (`./hpf audit --repo . --ref HEAD --changed main..HEAD --out /tmp/audit`), each command, and the limits (grade 2 is agreement of two agents, not a proof; a human owner decides what is a bug).

You cannot start Puppetmaster jobs from inside this task. Do not try. The pilot runs the live test.

Report at the end: the test command and its summary line, each deviation from this specification with the reason, and each thing that you did not test.
