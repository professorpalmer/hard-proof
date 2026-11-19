# hpflow audit of hard-proof-repo at 98f4a1cd8d52

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 3.

## Confirmed (3)

| Function | Found by | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/commands.py:place_claim` k=1 | hpf review | When the claim gives a function name and a line, and exactly one function has that exact name, place_claim takes it and ignores the line, even if the line is inside a different function (a method with the same short name). The claim is placed on the wrong function. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `('foo', [1, 2])` | An imported finding that gives a short method name plus a line inside that method is placed on a same-named top-level function, so the worker tests the wrong code and the claim is judged against the wrong target. | project/tool/hpflow/commands.py:640 |
| `tool/hpflow/commands.py:cmd_import` k=1 | hpf review | For a SARIF file the --source option replaces the tool name that the SARIF run itself gives (driver name), although --source is documented as the name of the tool only for a finding that does not give one. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `['mytool']` | With a SARIF file, `import --source X` overwrites the tool name the SARIF run gives, so findings from bandit are recorded as X, contradicting the documented fallback-only meaning of --source. | project/tool/hpflow/cli.py:180 |
| `tool/hpflow/outside.py:read` k=1 | hpf review | For a SARIF file, the `source` argument overrides the tool name that the file gives in tool.driver.name. The docstring and the --source help say `source` is only for an entry that does not give one (the hpflow form does this right). |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'other'` | With `import --findings x.sarif --source NAME`, every SARIF result is labelled NAME instead of the tool name in tool.driver.name, so the finding source is wrong, unlike the hpflow form. | project/tool/hpflow/commands.py:637 |

## Real but not reachable (0)

None.

## By design (0)

None.

## Mixed (2)

| Function | Found by | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/commands.py:report_md` k=1 | hpf review | cell() escapes '\|' but not a backslash before it, so text like 'a\\|b' becomes 'a\\\|b', where the pipe is not escaped (the backslash is). The Markdown table row gets an extra column. |  | claude-sonnet-5-5: real, claude-opus-5-5: unclear | `'\| `a.py:f` k=1 \| hpf review \| path a\\\\\|b \|  \| m: real \| `1` \|  \|  \|'` | A review claim, result_now or caller text containing a backslash before a pipe (e.g. a regex or shell snippet) is rendered as an escaped backslash plus a live pipe, so the REPORT.md table row gets an extra column and breaks. | project/tool/hpflow/commands.py:854 |
| `tool/hpflow/outside.py:file_of_uri` k=1 | hpf review | For a file: URI with a non-empty host part (file://C:/repo/a.py, a drive written as the authority), the host is silently dropped and only the path is returned, so the result names a different file. |  | claude-sonnet-5-5: unclear, claude-opus-5-5: None | `'/repo/a.py'` | For file://C:/repo/a.py the host is discarded and '/repo/a.py' is returned, but that form is a malformed file URI (RFC 8089 wants file:///C:/...), so whether it must be repaired is a decision. | project/tool/hpflow/outside.py:98 |
