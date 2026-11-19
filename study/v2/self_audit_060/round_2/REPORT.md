# hpflow audit of hard-proof-repo at c8508b11c680

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 3.

## Confirmed (3)

| Function | Found by | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/commands.py:cell` k=1 | hpf review | cell replaces only \\n, so a carriage return (or \\r\\n) in the text stays in the table cell. Markdown treats a lone CR as a line end, so it splits the table row. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'a\\rb'` | A carriage return in a claim, what_goes_wrong, caller or file name (taken from model JSON or git paths) stays in the cell, so REPORT.md splits the table row in viewers that treat a lone CR as a line end. | project/tool/hpflow/commands.py:896 |
| `tool/hpflow/outside.py:file_of_uri` k=1 | hpf review | The host `localhost` is matched case-sensitively, so `file://LOCALHOST/repo/a.py` is treated as another host and gives `//LOCALHOST/repo/a.py` instead of the local path. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'//LOCALHOST/repo/a.py'` | A SARIF artifact URI with host `LOCALHOST` (hosts are case-insensitive per RFC 3986/8089) is turned into the fake network path `//LOCALHOST/repo/a.py`, so the finding's file does not match the repository file. | project/tool/hpflow/outside.py:105 |
| `tool/hpflow/outside.py:sarif_entries` k=1 | hpf review | file_of_uri compares the host with 'localhost' case-sensitively, but host names are case-insensitive, so 'file://LOCALHOST/a.py' is treated as a file on another host and gives '//LOCALHOST/a.py'. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'//LOCALHOST/a.py'` | A SARIF result whose uri is file://LOCALHOST/a.py gets the file '//LOCALHOST/a.py' instead of '/a.py', so the finding does not match the repository file and is treated as another host's file. | project/tool/hpflow/outside.py:121 |

## Real but not reachable (0)

None.

## By design (0)

None.

## Mixed (0)

None.
