# hpflow audit of hard-proof-repo at c78d8efcbf59

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 0.

## Confirmed (0)

None.

## Real but not reachable (0)

None.

## By design (0)

None.

## Mixed (1)

| Function | Found by | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/cli.py:run_command` k=1 | hpf review | In `audit` without targets (for example `--findings` only), run_command passes args.group directly to cmd_verify. That value is the review default 'function', not read_group(), so it ignores the grouping in a stored review.json. The `verify` command does use read_group(). |  | claude-sonnet-5-5: real, claude-opus-5-5: intended | `{'group': 'function'}` | `audit --findings F` on an output folder whose review.json has group 'file' verifies by function (the audit default), not by the stored grouping, so the verify step groups differently from the review it checks. | project/tool/hpflow/cli.py:240 |
