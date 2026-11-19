# hpflow audit of hard-proof-repo at 72f53d4ae5d3

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 4.

## Confirmed (4)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/codexhome.py:first_key` k=1 | A quoted key that uses the TOML 8-digit \U escape is not decoded: json.loads rejects \U, so the fallback returns the raw text with the backslash escape still in it. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'\\U0000006dcp_servers'` | A user config.toml whose dropped table or key is spelled with a TOML \UXXXXXXXX escape (e.g. "\U0000006dcp_servers".x) is not recognized, so lean_config keeps the mcp_servers table that a worker must not inherit. | project/tool/hpflow/codexhome.py:137 |
| `tool/hpflow/codexhome.py:lean_config` k=1 | A quoted table name written with a TOML \UXXXXXXXX escape ("\U0000006dcp_servers" is mcp_servers) is not decoded. first_key falls back to the raw text when json.loads rejects \U, so the dropped table is kept. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'a = 1\n["\\U0000006dcp_servers".x]\nc = 1\n'` | A user config.toml with a table header written with a TOML \UXXXXXXXX escape (e.g. ["\U0000006dcp_servers".x]) keeps the mcp_servers table in the lean worker config, so workers inherit MCP servers that the lean home is meant to drop. | project/tool/hpflow/codexhome.py:212 |
| `tool/hpflow/common.py:run_snippet` k=1 | If the snippet writes to stdout without a final newline before run() returns, the JSON result line is glued to that text, so no line starts with '{' and run_snippet reports 'no output' even though run() succeeded. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `{'ok': False, 'error': 'no output', 'message': ''}` | A repro snippet (or the code it calls) that writes to stdout without a trailing newline glues the JSON result line onto that text, so run_snippet reports 'no output' and the repro is graded as a failure although run() succeeded. | project/tool/hpflow/commands.py:550 |
| `tool/hpflow/direct.py:parse_verdict` k=1 | The comment says only space, tab and CR are space around a line and any other character is content, but VERDICT_LINE uses \s, so a trailing NBSP (or form feed) is stripped and the line is accepted. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `('PASS', 'ok')` | A final line 'VERDICT: PASS - ok' followed by NBSP or form feed is accepted because VERDICT_LINE's \s* / \s*$ strip it, although the comment and test say only space, tab and CR are padding, so hpflow may read a verdict that Puppetmaster's parse_terminal_verdict rejects. | project/tool/hpflow/direct.py:399 |

## Real but not reachable (1)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/fixcheck.py:changed_files` k=1 | changed_files drops every path ending in .pyc (or inside a cache folder) even when the file is tracked in the commit and the worker modified or deleted it. The docstring says each path that differs from the commit is returned, so a real change of a committed file is hidden from the write-scope check |  | claude-sonnet-5-5: real_unreachable, claude-opus-5-5: None | `[]` | A committed .pyc or cache-folder file that the worker modifies or deletes is filtered out by name, so the write-scope check never sees it, which conflicts with the docstring. |  |

## By design (0)

None.

## Mixed (1)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/fixcheck.py:check` k=1 | check() only compares the repro result when the repro ran with ok=True. A repro that now crashes (the fix broke the module, so import or run() fails) is never reported, so the fix is accepted although the repro gives no valid new result. |  | claude-sonnet-5-5: unclear, claude-opus-5-5: None | `'accept'` | A repro that errors or times out after the fix adds no problem, so check() can accept a fix whose repro no longer returns a valid result (only the new test and related tests may catch it). |  |
