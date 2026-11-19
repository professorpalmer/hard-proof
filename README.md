# Hard Proof

A proof gate for agent-written code, an adversary that proves what the laws leave open, and an audit
method that takes review findings to fixes. This repository has the code, the Lean sources, the run
records and the tools of the study "Proved is not finished".

- **Read the study:** https://puppetmaster.gg/labs/hard-proof/ (summary) and
  https://puppetmaster.gg/labs/hard-proof/paper/ (paper). That page is the current version.
- **Paper as PDF:** [docs/paper.pdf](docs/paper.pdf)
- **Status:** a draft for review. An AI agent ran the study. The limits are in Section 17 of the paper.

## The idea in five sentences

A proof gate accepts a code change only when a checker accepts a machine-checked proof for each law
that a human owns. That forces "the code obeys the laws". It does not force "the laws say enough".
An adversary agent can prove what the laws leave open: it supplies two designs that pass each law and
one input on which they differ. That gap becomes one concrete question for the human, the answer
becomes a new law, and the loop stops when the checker accepts a proof that no gap is left.

## What the data says

Each number is in the paper, with the command that gives it.

| Result | Evidence |
| --- | --- |
| Agents find gaps and prove completeness with machine-checked certificates | 73 gap certificates and 66 completeness proofs in 144 adversary runs of the first study |
| A plain review finds most gaps for the same cost | 22 of 27 gaps at 48 decision points, with no proof |
| The proof duty finds a gap that review misses | One fault in a definition: 0 of 12 reviews, 3 of 3 proof runs |
| A review loop can stop early; a proof loop ends on a theorem | A review loop "until dry" ended on a false "complete" in 3 of 6 law sets |
| Durable sessions make later rounds cheap | A later round costs $0.06 to $0.31, a first visit $0.40 to $0.49 |
| A pointed agent review misses more than half of real bugs | The best of three review arms found 44 of 95 real bugs of two products |
| A full proof pipeline does not replace a review, and it finds different bugs | 31 of 95 for about 8 times the cost of the best review arm; 6 of the 40 bugs that three review arms missed |
| An audit ladder turns review findings into fixes | 211 findings gave 45 confirmed bugs; 51 fixes shipped in Puppetmaster 1.51.2 and Marionette 0.9.685 |
| A conflict between code and a law is most often a fault of the law | 73 live conflicts from the pipeline: 0 reachable bugs, 3 latent faults, 2 wrong documentation sentences, 57 laws that say more than the sentence |
| A small decision rule gets a completeness proof in minutes | The swarm policy table of Marionette: 5 laws, 16 input cases, accepted by 6 kernels; its docstring alone left one input open |

The study also reports what did not work: one of its own "blind" tests was not blind, a fix step with
a test and a judge let 5 of 45 wrong fixes through, a runner fault ran six bugs of the pipeline test two times, and the runs took the test machine down one time.

## Use it on your code

Our recommendation from the data has three rules. Section 14 of the paper has the reasons and the costs.

1. **For all code: a review with receipts.** No finding counts without a repro that a script runs, and two
   verifier agents must each name a caller. `hpf` does these steps for the functions that changed in a git range.
2. **For a rule that the owner states: a proof.** A decision table, a permission rule, a price rule, a lock.
   `hp` is the proof gate for one Python function.
3. **Do not use laws that an agent writes from documentation as a bug finder for old code.** It costs more than
   a review, and most of its conflicts are faults of the law.

Install the two tools (Python 3.9 or later, no dependency):

```bash
pip install hpflow
```

The package name is `hpflow`. The name `hardproof` on PyPI is a different project that is not related to this work.

Audit the functions that changed since a tag, and gate the release:

```bash
hpf audit --repo . --ref HEAD --changed v1.2.3..HEAD --out ~/audits/next
hpf fix   --out ~/audits/next      # only when REPORT.md has confirmed bugs
hpf gate  --out ~/audits/next --ref HEAD
```

- `hpf audit` and `hpf fix` start agent workers. They need the Puppetmaster command line
  (`pip install puppetmaster-ai`) and Claude Code with a login.
- `hpf fix` never commits. Review each fix and merge it yourself.
- `hpf gate` makes no model call. It passes when each confirmed bug gives a new result on the commit that you
  release, or has a waiver with a reason (`hpf waive`).
- Measured cost on our products: about 1.40 US dollars for each changed function for the review and the two
  verifiers, and 36 US dollars for one release range of 20 functions with its 7 fixes (API-equivalent).

For a proof of one function, start with `tool/README.md` (the domain contract and a quick start on
`tool/examples/clamp`). `v3/swarm_policy` is a real decision table as a complete domain: 5 laws, a proof that
the code passes them, and a proof that the laws leave no input open.

A pass of the gate does not say that the code has no bug. The tools are a first version: Python functions,
Claude models, and tests on our own two products only.

## What is in this repository

| Folder | Content |
| --- | --- |
| `exp1` to `exp12`, `reps` | The experiments of the first study: Lean models, laws, challenge files, gate scripts, link tests, each run folder with the worker solution |
| `baseline` | The review with no proof duty at 48 decision points, the audit of worker transcripts, and the second run of the blind tables |
| `v2` | The loop tests, the data set of 95 real bugs, the review arms, the proof pipeline on real bugs, the audit of findings, and the fix records |
| `v3` | The first proof on a new product function: the swarm policy table of Marionette |
| `tool/hpflow/proof` | The command `hp`: one proof gate for one Python function: model, link test, laws, and four kinds of certificate |
| `tool/hpflow` | The audit ladder as one command set: targets from a git range, review, script gate, two verifiers, fix, and the release gate |
| `site` | The build scripts of the paper and of this PDF |
| `docs` | The paper as PDF and as a print page |

## Quick start

Check each stored proof of the first study again. This makes no model call.

```bash
python3 verify_all.py
```

Try the proof gate on a small example.

```bash
cd tool/examples/clamp && ../../hp check model && ../../hp check laws && ../../hp check ref
```

Run the tests of the two tools.

```bash
cd tool && python3 -m unittest discover tests
```

`tool/README.md` has the domain contract and each command. `hpflow` needs the Puppetmaster command
line (`pip install puppetmaster-ai`) and an agent adapter. Its tests need neither.

## What the audit ladder is, and what it is not

`hpflow` takes Python functions up a ladder of evidence: a finding with a runnable repro, a script
check on the source under audit, two verifier agents on different models that must name a caller, a
fix with a regression test and a judge, and a second review with CI. No step of this ladder is a Lean
proof. Each grade below a proof is agreement of agents, a script, or CI. The owner of the code decides
what is a bug.

## License

MIT. See [LICENSE](LICENSE).

## Requirements

- Lean 4.36.0 (`elan` reads `lean-toolchain` in each folder). No Mathlib.
- Python 3.11 or later for the study scripts. The two tools in `tool/` need Python 3.9 or later.
- For the link tests: a checkout of Puppetmaster (https://github.com/professorpalmer/Puppetmaster).
- The comparator sandbox needs `bwrap` (Linux). On a host with no `bwrap`, each gate adds
  `--inadvisably-no-sandbox`. Run untrusted Lean code only in a sandbox.

## Check each stored result

```bash
python3 verify_all.py
```

This command runs each gate again on each stored worker result, with the extra
kernels, and compares the verdict with the run record. It makes no model call.
The output goes to `verify_all.json`.

## Where each claim is

| Claim in the paper | Folder | Command |
| --- | --- | --- |
| The pid-only lock obeys law 1 and breaks law 2 | `exp1` | `python3 gate.py check --paranoid` |
| Eleven cheat attempts against the gate | `exp1` | `python3 attacks.py` |
| Link test of the lock model against the real lock | `exp2` | `python3 conformance.py --traces 20000 --seed 1 --pm <Puppetmaster checkout>` |
| Link test against five real releases | `exp9` | `PM_REPO=<Puppetmaster checkout> sh history.sh <scratch dir>` |
| The challenge with no start token is impossible | `exp4` | `lake build` in `exp4`, theorem `Exp4.challenge_is_impossible` |
| Gap certificates for three lock laws | `exp6`, `reps/exp6_gap*` | `python3 gap_gate.py check --paranoid` in a run folder |
| Completeness for four lock laws | `exp7`, `reps/exp7_complete*` | `python3 complete_gate.py check --paranoid` |
| Laws 1, 2 and 4 are sufficient for the lock | `exp7/evidence/pilot_three_laws` | `lake build && lake env lean Axioms.lean` |
| Seven sync laws proved with no example | `exp8/a_*`, `reps/exp8a_code*` | `python3 gate8.py check code --paranoid` |
| Link test of the sync model against the real function | `exp8/base` | `python3 sync_link.py --cases 200000 --seed 1 --pm <Puppetmaster checkout>` |
| Gap certificates for seven sync laws | `exp8/c_*`, `reps/exp8c_gap*` | `python3 gate8.py check gap --paranoid` |
| Completeness for eight sync laws | `exp8/d_*`, `reps/exp8d_complete*` | `python3 gate8.py check gap complete --paranoid` |
| Agent-written laws for the recovery rule, and the loop | `exp10/a_*`, `exp10/loop2_*` | `python3 gate10.py check laws`, `python3 gate10.py check gap complete --paranoid` |
| Link test of the recovery rule | `exp10/base` | `python3 recover_link.py --pm <Puppetmaster checkout>` |
| Generated rules, reference rule visible | `exp11/k*`, `reps/exp11_k*` | `python3 gate11.py check gap complete --paranoid` |
| Generated rules, blind | `exp11/b*`, `reps/exp11b_b*` | `python3 gate11.py check gap complete --paranoid` |
| Agent-written laws for the sync command, and the loop | `exp12/a_*`, `exp12/loop_*` | `python3 gate12.py check laws`, `python3 gate12.py check gap complete --paranoid` |
| The kinds of gap | `reps` | `python3 classify.py` |
| Reviews with no proof duty at 48 decision points | `baseline` | `python3 baseline.py score` (reads the stored answers in `baseline/results_*.json`) |
| The blind tables again in neutral folders | `baseline/results_proof.json`, `baseline/proof_runs` | `python3 gate11.py check gap complete --paranoid` in a run folder |
| Audit of worker transcripts for an answer leak | `baseline/audit.py` | `python3 audit.py <run folder>` (needs the transcripts of the host that ran the workers) |
| A review loop "until dry" against the proof loop | `v2/reviewloop`, `v2/reviewloop.py` | the stored records `v2/reviewloop/*.json` |
| The proof loop as one durable flow, cost of each visit | `v2/durable`, `v2/durable_loop.py` | the stored records `v2/durable/*.json` |
| The data set of 95 real bugs | `v2/bugs.json`, `v2/bugs.py` | `python3 bugs.py trees` then `python3 bugs.py verify` runs each repro on the source before and after the fix (needs checkouts of the two products) |
| Detections of the three review arms | `v2/review_detected.json` | ids only; the text of each finding is not in this repository |
| The proof pipeline on the 95 bugs, and the comparison with the review arms | `v2/retro/*.json`, `v2/retro.py` | `python3 retro_compare.py` (reads the stored results, makes no model call) |
| The audit of the conflict certificates of the pipeline | `v2/conflict_audit.py`, `v2/conflict_groups.json`, `v2/conflict_verdicts.json`, `v2/conflict_triage.json` | the stored records (the two verdicts for each conflict; the text of each verifier is not in this repository) |
| The audit ladder: findings, verdicts, fixes | `v2/ladder_summary.json`, `v2/confirmed_bugs.json`, `v2/CONFIRMED_BUGS.md`, `v2/fix_runs.json` | the stored records |
| The release gate on a stored audit: fail on the audited release, pass on the next | `v2/gate_live.json` | `hpf gate --out <audit folder> --ref <tag>` (needs the audit folder and a checkout of Puppetmaster) |
| The proof of the swarm policy table | `v3/swarm_policy`, `v3/swarm_policy_docstring` | `python3 v3/summarize.py --repo <Marionette checkout>` |

`exp11/meta/` has the removed law of each generated task. The workers did not have this folder.

The run folders of the blind set (`reps/exp11b_*`) have the word `gap` or `complete` in their name.
The workers ran in these folders, so the path told the kind of result. `baseline/proof_neutral.py`
ran the Haiku and Sonnet tasks again in folders with a hash for a name.

`baseline/answers/<arm>/<id>.json` has each review answer. `baseline/tasks.json` maps each id to its
decision point, and `baseline/judgments.json` has the pilot's reading of each gap answer that a
script cannot check.

`exp10/loop_*` (without the `2`) is a first set of loop runs that is void for a harness reason:
Lean wrote `lake-manifest.json` outside the write scope of the worker, and each flow reported
"failed". The worker results in that set are valid, but the paper reports the second set.

`reps/failed_cursor/` has 8 run records that stopped at launch with an account message from the
provider. No model ran.

## Run records

- `reps/*.json`: one record for each worker run: flow id, visits, worker verdicts, worker time,
  cost, changed files, and the verdict of the pilot gate.
- `exp10/loop2_*/result.json`, `exp12/loop_*/result.json`: one record for each loop: each round,
  each question, each answer, each new law.

The flows ran on Puppetmaster 1.51.0 with the Claude Code and Codex adapters. To run a flow
again, use `reps/run_reps.py`, `exp10/loop10.py` or `exp12/loop12.py`. A new run makes model calls.
