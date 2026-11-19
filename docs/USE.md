# Use the tools

`hpflow` is one package with two commands: `hpf` (the audit ladder with a release gate) and `hp` (the proof
gate for one Python function). It is on PyPI: https://pypi.org/project/hpflow/

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

- `hpf audit` and `hpf fix` start agent workers. They need one agent tool with a login, and no other
  package: Claude Code (the default), Codex (`--adapter codex`), or another tool through a command template
  (`--adapter command --agent-cmd`). [`tool/README.md`](../tool/README.md) has an example for each.
- `hpf fix` never commits. Review each fix and merge it yourself.
- `hpf gate` makes no model call. It passes when each confirmed bug gives a new result on the commit that you
  release, or has a waiver with a reason (`hpf waive`).
- Measured cost on our products with version 0.5: about 0.27 US dollars for each changed function for the
  review and the verifiers (5.38 US dollars for a release range of 20 functions, the mean of three runs,
  API-equivalent), in about 7 minutes. Version 0.4 cost 9.44 US dollars for the same range, and the first
  form of the tool cost 28.53.
- A worker is lean by default: it has six tools, and it does not load the Claude Code settings, rules, MCP
  servers and skills of the user. `--user-settings` gives each worker the full profile.
- To run the audit for a pull request in CI, see `.github/workflows/hpf-audit.yml` of this repository: it runs
  when the pull request has the label `hpf-audit`, and it fails when the gate fails.

For a proof of one function, start with [`tool/README.md`](../tool/README.md) (the domain contract and a quick start on
`tool/examples/clamp`). `study/v3/swarm_policy` is a real decision table as a complete domain: 5 laws, a proof that
the code passes them, and a proof that the laws leave no input open.

A pass of the gate does not say that the code has no bug. The tools are a first version: Python functions,
most runs on Claude models, and tests on our own products only.

## Try the proof gate and run the tests

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

`tool/README.md` has the domain contract and each command. `hpflow` needs one agent tool with a login.
Its tests need none.

## What the audit ladder is, and what it is not

`hpflow` takes Python functions up a ladder of evidence: a finding with a runnable repro, a script
check on the source under audit, two verifier agents on different models that must name a caller, a
fix with a regression test and a judge, and a second review with CI. No step of this ladder is a Lean
proof. Each grade below a proof is agreement of agents, a script, or CI. The owner of the code decides
what is a bug.
