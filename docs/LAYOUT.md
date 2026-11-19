# Repository layout

## Folders

| Folder | Content |
| --- | --- |
| `study/exp1` to `study/exp12`, `study/reps` | The experiments of the first study: Lean models, laws, challenge files, gate scripts, link tests, each run folder with the worker solution |
| `study/baseline` | The review with no proof duty at 48 decision points, the audit of worker transcripts, and the second run of the blind tables |
| `study/v2` | The loop tests, the data set of 95 real bugs, the review arms, the proof pipeline on real bugs, the audit of findings, and the fix records |
| `study/v3` | The first proof on a new product function: the swarm policy table of Marionette |
| `tool/hpflow/proof` | The command `hp`: one proof gate for one Python function: model, link test, laws, and four kinds of certificate |
| `tool/hpflow` | The audit ladder as one command set: targets from a git range, review, script gate, two verifiers, fix, and the release gate |
| `site` | The build scripts: `build_site.py` (the paper and the public data file), `build_page.py` (the study page, with its style and script in `site/page`), `build_pdf.py` (this PDF) |
| `docs` | The guides of this repository, and the paper as PDF and as a print page |

## Requirements

- Lean 4.36.0 (`elan` reads `lean-toolchain` in each folder). No Mathlib.
- Python 3.11 or later for the study scripts. The two tools in `tool/` need Python 3.9 or later.
- For the link tests: a checkout of Puppetmaster (https://github.com/professorpalmer/Puppetmaster).
- The comparator sandbox needs `bwrap` (Linux). On a host with no `bwrap`, each gate adds
  `--inadvisably-no-sandbox`. Run untrusted Lean code only in a sandbox.

## Run records

The paths in this section are in `study/`.

- `reps/*.json`: one record for each worker run: flow id, visits, worker verdicts, worker time,
  cost, changed files, and the verdict of the pilot gate.
- `exp10/loop2_*/result.json`, `exp12/loop_*/result.json`: one record for each loop: each round,
  each question, each answer, each new law.

The flows ran on Puppetmaster 1.51.0 with the Claude Code and Codex adapters. To run a flow
again, use `reps/run_reps.py`, `exp10/loop10.py` or `exp12/loop12.py`. A new run makes model calls.
