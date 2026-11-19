# hpflow audit of hard-proof at 0dc8aa75f567

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 2.

## Confirmed (2)

| Function | Found by | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/cli.py:main` k=1 | hpf review | The audit pre-check ("a usage error must come before the workers of the review run") does not check that --models gives two or more distinct models, which cmd_verify requires. So `audit ... --models sonnet` runs init, targets and review (starting workers) and only then fails in verify. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `(1, 1, None, ['init', 'targets', 'review'])` | `hpflow audit --models sonnet` (or a repeated model) passes the pre-check, runs init, targets and the paid review workers, and only then fails in verify with 'verify needs two models or more', wasting the review cost. | project/tool/hpflow/__main__.py:7 |
| `tool/hpflow/commands.py:cmd_import` k=1 | hpf review | A SARIF result whose artifact uri is not a valid URL (for example 'file://[bad/x.py') makes urlsplit raise ValueError inside file_of_uri. outside.read does not catch it, so the whole import call crashes instead of skipping that one entry with a reason, as the module docstring promises. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `ValueError` | One SARIF result with a malformed artifact uri (e.g. 'file://[bad/x.py') makes urlsplit raise ValueError, so the whole import command crashes and no other finding in the file is imported. | project/tool/hpflow/cli.py:180 |

## Real but not reachable (0)

None.

## By design (1)

| Function | Found by | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/cli.py:run_command` k=1 | hpf review | For `verify` with no --group and no stored review.json, run_command passes group 'function' (via read_group), but read_group's docstring says the fallback is `file`. |  | claude-sonnet-5-5: intended, claude-opus-5-5: None | `'function'` |  |  |

## Mixed (1)

| Function | Found by | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/cli.py:add_audit_targets` k=1 | hpf review | add_audit_targets accepts --max -1 (and 0) without a usage error, although the module has positive_int for whole numbers of 1 or more; every target is then silently skipped as over --max. |  | claude-sonnet-5-5: real, claude-opus-5-5: unclear | `(-1, 150)` | `audit --file a.py --max -1` (or 0) is accepted and then every target is skipped as 'over --max', so the audit does nothing instead of giving a usage error. | project/tool/hpflow/cli.py:212 |
