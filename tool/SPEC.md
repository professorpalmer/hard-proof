# hardproof: one tool for the proof gate

Status: specification for the first version. Owner of this file: the pilot.

## Purpose

The study in `~/Projects/hard-proof` has one hand-written gate script for each
experiment (`exp12/base/gate12.py` is the latest and the best reference, with
`exp12/base/*.lean`, `exp12/base/sync_link.py`, `exp12/loop12.py`). This tool
replaces them with one command set and one domain contract, so that a new
Python function gets a proof gate with no new gate code.

## Rules for the code

- Python 3.9+, stdlib only, `from __future__ import annotations`, no emojis, JSON not YAML.
- Lean 4.36.0, no Mathlib. `lake comparator` does the statement match, the axiom audit and the kernel replay.
- All prose (docstrings, help, README, messages) in short plain sentences. No contractions.
- The package is `hardproof/` in this folder. It runs as `python3 -m hardproof <command>` with `PYTHONPATH` set to this
  folder, and as `./hp <command>` (a small launcher script). The current folder is the domain folder, or `--dir PATH`.
- Each command prints one JSON report to stdout and returns 0 for accept and 1 for reject, 2 for usage errors.
- Each `check` appends one line to `hardproof_runs.jsonl` in the domain folder (time, actor from `--actor`, command, verdict, seconds).

## The domain contract

A domain is one folder for one function under test. A function under test has
the type `Impl := Input → Output` in Lean. A stateful system is out of scope for
this version (its author can put the state into `Input`).

Author files (an agent or a human writes them; after that they are pinned):

| File | Content |
| --- | --- |
| `hardproof.json` | `{"name": "...", "namespace": "HP", "python": {"module": "pkg.mod", "function": "name"}, "banned_in_laws": ["ref", ...]}` |
| `Types.lean` | namespace `HP`: `Input`, `Output` (each with `DecidableEq`), `abbrev Impl := Input → Output`, `def legal : Input → Bool`, `def Legal (x : Input) : Prop := legal x = true`, and the words that a law can use. No `ref` here. |
| `Ref.lean` | imports `Types`. `def HP.ref : HP.Impl`, the mirror of the Python code, and its helper functions. |
| `Codec.lean` | imports `Types`. `HP.decodeInput : String → Option Input`, `HP.encodeInput : Input → String`, `HP.encodeOutput : Output → String`, `HP.showInput : Input → String`, `HP.showOutput : Output → String`. One line of text for each value. `decodeInput (encodeInput x) = some x` is tested, not proved. |
| `link_adapter.py` | `gen(rng) -> case`, `encode(case) -> str` (the same line format as `encodeInput`), `decode(line) -> case`, `call(func, case) -> result` (calls the real Python function; it can simulate small state), `encode_result(result) -> str` (the same format as `encodeOutput`), `is_legal(case) -> bool`. |
| `DESCRIPTION.md` | The sentences of the documentation of the function, each an exact quote with its source file. Then a section that maps the model words to the documentation words. |
| `Laws.lean` | imports `Types` only (the gate rejects any other import). One `def <Name> (f : Impl) : Prop` for each law, `def Passes (f : Impl) : Prop` as the conjunction of all laws, and `theorem some_design_fails : ∃ f : Impl, ¬ Passes f`. |

Solution files (an untrusted agent writes them; the comparator checks them against generated challenge files):

| File | Challenge statement |
| --- | --- |
| `RefPassesSolution.lean` | `theorem HPRef.ref_passes : Passes ref` |
| `ConflictSolution.lean` | `def HPConflict.input : Input`, `theorem HPConflict.input_legal : Legal input`, `theorem HPConflict.ref_breaks : ¬ <Law> ref` for ONE named law. The file starts with the comment line `-- hardproof-law: <Law>`; the tool generates the challenge for that law. If a law has no input quantifier the `input` is still required and is shown to the human as the witness. |
| `GapSolution.lean` | `def HPGap.designA : Impl`, `def HPGap.designB : Impl`, `def HPGap.input : Input`, `theorem HPGap.a_passes : Passes designA`, `theorem HPGap.b_passes : Passes designB`, `theorem HPGap.input_legal : Legal input`, `theorem HPGap.differ : designA input ≠ designB input` |
| `CompleteSolution.lean` | `theorem HPComplete.laws_complete : ∀ f g : Impl, Passes f → Passes g → ∀ x : Input, Legal x → f x = g x` |

Tool-owned generated files (the tool writes them into the domain folder under `hp/`, and can write them again at any time): `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, the challenge modules, the comparator configs, `Runner.lean` (reads encoded inputs from stdin, prints `encodeOutput (ref x)` for each line, or `DECODE_ERROR`), `QuestionRunner.lean`.

Design the lakefile so that a broken solution file of one kind does not stop the check of another kind (one `lean_lib` for each solution, as in `exp12/base/lakefile.toml`).

## Commands

- `new DIR --name NAME --module PKG.MOD --function NAME`: make the domain folder with the generated files and with author
  stubs that hold short instructions as comments.
- `generate`: write the tool-owned files again.
- `check model`: `Types`, `Ref`, `Codec` and `Runner` build. No `sorry`, no `axiom`, no `native_decide`. The codec round trip
  holds on 200 generated cases from `link_adapter.gen` (`decode(encode(c)) == c`, and the Lean runner decodes each line).
- `link --repo PATH [--cases N] [--seed N] [--mutants N] [--function-file PATH]`: the link test. For each generated legal case,
  the Lean `ref` and the real Python function (imported from `PATH`) must give the same output line. Then the mutation part:
  the tool makes up to N mutants of the source of the Python function with its own AST mutator (negate a condition, swap
  `and`/`or`, change a comparison operator, change an integer constant by one, replace a `return` value by a default, delete
  one statement, swap two arguments of the same call when names permit), loads each mutant in place of the function, and
  runs the same cases. The report has: cases, differences (must be 0), the first difference, mutants made, mutants killed
  (at least one case differs or the mutant raises), and the list of mutants that survive with their one-line description.
  The verdict is `agree` only when differences is 0. The kill rate is reported, not judged.
- `check laws`: text rules (imports `Types` only, no banned word from `hardproof.json` before `theorem some_design_fails`, no
  `sorry`/`axiom`/`native_decide`), builds, the statements of `Passes` and `some_design_fails` have the right types, axiom
  audit (`propext`, `Quot.sound`, `Classical.choice` only), and the list of law names in the report.
- `check ref` / `check conflict` / `check gap` / `check complete` (more than one kind can be named; accept when one is
  accepted): build the solution, make sure each required name exists (the comparator of Lean 4.36.0 exits with 134 on an
  absent theorem, so the tool checks names first), then `lake comparator --config ...` with `--paranoid` when the flag is
  given, and `--inadvisably-no-sandbox` when `bwrap` is absent. For `conflict`, also check that the named law is a law of
  `Laws.lean`.
- `question`: for an accepted gap or conflict, print JSON with the encoded input, the shown input, and for a gap the shown
  and encoded output of design A, design B and `ref`; for a conflict the law name and the shown and encoded output of `ref`.
- `pin`: write `hardproof.lock.json` with the SHA-256 of each author file and each generated file. `verify-pins`: reject when
  one differs. A flow graph can also carry these hashes; `verify-pins --expect FILE=SHA ...` checks given values.
- `status`: one JSON summary: what exists, what the last check of each kind said.

## Tests (the acceptance for this work)

1. `tests/` with `unittest` tests that need no model call and run in less than 10 minutes with a warm build cache
   (`python3 -m unittest discover tests`).
2. An example domain `examples/sync/` that is the sync command of experiment 12 in this contract (`Input` is a structure
   of config fields, starter list and registry; `Legal` is the corrected rule: pairwise distinct starter ids). Port the
   model, the codec and the link adapter from `exp12/base`. Write a `Laws.lean` with the seven natural laws and NO law for
   the order of the new rows. The tests must show on this example:
   - `check model` accepts. `link --repo ~/Projects/hp-work/Puppetmaster` (function
     `puppetmaster.registry_sync.plan_starter_sync` plus the append, see `exp12/base/sync_link.py` for the adapter and the
     starter list simulation) agrees on 20,000 cases and kills at least one generated mutant. If that clone is absent the
     link test is skipped with a message.
   - `check laws` accepts. `check ref` accepts a correct `RefPassesSolution.lean`.
   - `check gap` accepts a gap certificate (the order of the new rows), and `question` prints the two results.
   - With one more law for the order, `check complete` accepts a completeness proof, and `check gap` rejects the old certificate.
   - With a deliberately false law (for example "new rows are always enabled"), `check conflict` accepts a conflict certificate
     and `check ref` cannot be accepted.
   - Attacks are rejected: `sorry` in a solution, a new axiom, `native_decide`, a solution that proves a different statement,
     a `Laws.lean` that imports `Ref`, a `Laws.lean` that names `ref`, an edited pinned file (`verify-pins`).
3. A second, very small example `examples/clamp/` for a pure function `clamp(x, lo, hi)` over integers defined in
   `examples/clamp/pycode/clampmod.py`, with a link test against it, to show a domain with no outside repository.
4. `README.md`: what the tool is, the contract table, a quick start that works on `examples/clamp`, and each command.

Report at the end: the command to run the tests and its output summary, each deviation from this specification with the
reason, and each thing that does not work. Do not claim a check that you did not run.
