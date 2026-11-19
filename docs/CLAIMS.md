# Where each claim is

Each claim of the paper has a folder and a command in this file.

The study is in the folder `study/` of this repository. Each folder in this file is in `study/`, and each
command runs from there.

## Check each stored result

```bash
cd study && python3 verify_all.py
```

This command runs each gate again on each stored worker result, with the extra
kernels, and compares the verdict with the run record. It makes no model call.
The output goes to `verify_all.json`.

## Claims and commands

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
| One release range, three review tools, one blind verify step | `v2/h2h` (rules in `PROTOCOL.md`, result in `result.json`) | `python3 h2h.py summary` in `v2` (reads the stored verdicts, makes no model call) |
| Three audits of one range with different session settings | `v2/cost_cut.json`, `v2/cost_cut.py` | `python3 cost_cut.py` (needs the three audit folders) |
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
