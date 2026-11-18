# hardproof

hardproof is one proof gate for one Python function. It replaces the
hand-written gate scripts of the Hard Proof study (`exp12/base/gate12.py` and
the scripts before it) with one command set and one domain contract. A new
Python function gets a proof gate with no new gate code.

The tool uses Lean 4.36.0 with no Mathlib. `lake comparator` does the
statement match, the axiom audit and the kernel replay. The tool is Python 3.9+
with the standard library only. It makes no model call.

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
`examples/clamp/pycode/clampmod.py`. It needs no outside repository.

1. Copy the example to a new folder and go to it:

   ```sh
   cp -R examples/clamp /tmp/clamp-demo
   cd /tmp/clamp-demo
   ```

2. Set `HP` to the launcher of this folder, for example
   `HP=~/Projects/hard-proof/tool/hp`.
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
`python3 -m hardproof <command>` with `PYTHONPATH` set to this folder, or as
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

`hpflow` is the second package of this folder. It runs agent workers through
the Puppetmaster command line and takes a set of Python functions up an
evidence ladder. `hardproof` makes no model call. `hpflow` does.

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

### Commands

All commands take `--out DIR` (the audit folder), `--redo` and
`--concurrency N` (default 5: the most worker flows that run at one time).
Each command that `hpflow` starts (a repro, a test run, git) runs in its own
process group with a timeout. At the timeout the whole group ends. Run them as `./hpf <command>` or as
`python3 -m hpflow <command>` with `PYTHONPATH` set to this folder. Each
command prints one JSON report. The exit code is 0 on success, 1 on a failed
step, and 2 on a usage error.

All state is in the audit folder, as JSON files. A command can run again: it
does not repeat a worker run that has a stored result. `--redo` makes the
runs again. A stored run with an error (launch or wait) runs again.

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
- `review [--model sonnet] [--shell | --no-shell] [--passes 1] [--repro-timeout 60]`:
  one reviewer run for each target and pass. Each finding has a repro file
  `finding_<n>.py` with `run()`. A script runs each repro on `src/` in a
  separate process. A finding has grade 1 when `run()` returns. Else it stays
  at grade 0 with the reason (no repro file, an import error, a timeout, or
  an exception).
- `verify [--models opus sonnet]`: one verifier run for each target with
  grade-1 findings and each model. A finding has grade 2 when each verifier
  says `real`. Duplicates fold into one bug (the `duplicate_of` field of the
  first model). Writes `verify.json`, `confirmed.json` and `REPORT.md` (one
  table for each class: confirmed, real but not reachable, by design, mixed).
- `fix [--base REF] [--only BUG ...] [--model opus] [--judge-model sonnet] [--rules TEXT]`:
  for each source file with confirmed bugs, a git worktree `fix/<slug>` on a
  new branch `hpfix/<slug>` from `--base` (default: the audited commit), in
  the audited repository. A build worker writes the fix and the test file
  `tests/test_hpfix_<slug>.py`. A script check (`python3 -m hpflow.fixcheck`)
  runs each repro (it must give a new result), the new test file and the
  related tests. A judge reviews the diff with a rubric. A failed check or a
  FAIL or PARTIAL review goes back to the builder. `hpflow` never commits,
  pushes or merges. The report lists each worktree, its diff stat, its new
  files, the check verdict and the judge verdict.
- `audit ...`: `init`, `targets`, `review` and `verify` in one call, with the
  options of each. It stops at the first step that fails.
- `status`: the count of findings at each grade, the cost and time of each
  step, and what is not done.

Model names: `haiku`, `sonnet` and `opus` map to `claude-haiku-5-5`,
`claude-sonnet-5-5` and `claude-opus-5-5`. A full model id passes through.
The adapter is `claude-code`.

Workers get a snapshot of the source, never the repository of the user. Each
run folder is `runs/<digits>`, and each worker gets a copy of `src/` as
`project/`. The name holds no word and no function name.

Cost is API-equivalent, as the provider tool reports it. Plan billing can
apply. The tool reports the cost of a resumed session as the total of the
session so far. So the cost of a node is the largest value of its visits, and
the cost of one visit is the difference from the visit before it.

### Limits

- Grade 2 is the agreement of two agents. It is not a proof.
- A human owner of the code decides what is a bug, and reviews and commits
  each fix.
- Grade 1 shows only that the repro runs and gives a result. It does not show
  that the result is wrong.
- Lean certificates (the `hardproof` gate) are not part of the ladder yet.
