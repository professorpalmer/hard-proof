# hpflow audit of hard-proof-repo at 6e775a10ed64

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 5.

## Confirmed (5)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/codexhome.py:toml_scan` k=1 | A multi-line string whose content ends with a quote character (TOML closes it with 4 or 5 quotes, e.g. a = ["""x""""]) is closed at the first three quotes; the extra quote starts a basic string that swallows the following ']' so depth stays 1. Same for ''' literal strings. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `(1, None)` | A multi-line string ending in a quote (valid TOML, e.g. a = ["""x""""]) leaves depth at 1, so lean_config treats following lines as inside an array and a later top-level `notify = ...` key is not dropped from the worker's config. | project/tool/hpflow/codexhome.py:174 |
| `tool/hpflow/commands.py:cmd_targets` k=1 | In --changed mode, a function whose last body lines were deleted is missed when git reports the deletion as a mixed hunk (old lines removed and a new line added right after the function, e.g. a comment replacing the blank line). hunk_ranges records no deleted_ranges for a mixed hunk and the new line |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `[]` | When a commit removes the last lines of a function and adds a line just outside it (a mixed hunk), `hpflow targets --changed A..B` leaves out the changed function, so it is never reviewed. | project/tool/hpflow/cli.py:152 |
| `tool/hpflow/commands.py:changed_files` k=1 | The per-file `git diff` gets the file name as a pathspec, so glob characters in a name (e.g. `a*.py`) are expanded. The diff of that file then also includes other files that match (`ab.py`), and their hunks are added to its ranges. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `[('a*.py', [(2, 2), (2, 3)]), ('ab.py', [(2, 3)])]` | A changed file whose name has glob characters (*, ?, [) gets the hunks of other files that match its name as a pathspec, so `hpflow targets --changed` picks functions that did not change in that file. | project/tool/hpflow/commands.py:360 |
| `tool/hpflow/commands.py:hunk_ranges` k=1 | hunk_ranges splits the diff with str.splitlines(), which also breaks at form feed, \x1c-\x1e, \x85 and \u2028/\u2029. A changed line that holds such a character followed by text like '@@ -50 +50 @@' is read as a hunk header, so a fake range is added. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `{'old_ranges': [(3, 3), (50, 50)], 'new_ranges': [(3, 3), (50, 50)], 'deleted_ranges': []}` | A changed source line containing a form feed, \x1c-\x1e, \x85 or \u2028/\u2029 followed by text like '@@ -50 +50 @@' is split into its own line by splitlines() and read as a hunk header, adding a fake range so unrelated functions are reported as changed. | project/tool/hpflow/commands.py:305 |
| `tool/hpflow/fixcheck.py:check` k=1 | check() runs at most 12 related test files (related[:12]) and silently drops the rest without reporting them, so a failing related test beyond the first 12 is never run and the change is accepted although the docstring requires that the tests naming the changed module must pass. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'accept'` | When more than 12 repository tests name the changed module, the extras are dropped without a word, so a fix that breaks one of them is accepted although the contract says the related tests must pass. | project/tool/hpflow/commands.py:778 |

## Real but not reachable (2)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/codexhome.py:lean_config` k=1 | DROPPED_TABLE ends the table name with \b, so a different table whose name merely starts with a dropped name followed by a hyphen (e.g. [plugins-extra], [hooks-x]) is treated as a dropped table and removed from the lean config. |  | claude-sonnet-5-5: real_unreachable, claude-opus-5-5: None | `'model = "m"\n[profiles.p]\ny = 2\n'` | A valid TOML table such as [plugins-extra] or [hooks-x] is silently removed from the worker's lean config because \b matches before a hyphen, although only the exact tables and their sub-tables are meant to be dropped. |  |
| `tool/hpflow/fixcheck.py:imports_module` k=1 | A source that is too complex for the parser (a deeply nested expression) raises MemoryError (or RecursionError) out of imports_module, because only SyntaxError and ValueError are caught. The docstring says a file that does not parse is not related, so it should return False. The caller in check() wo |  | claude-sonnet-5-5: real_unreachable, claude-opus-5-5: None | `MemoryError` | A source nested too deeply for the parser raises MemoryError or RecursionError out of imports_module, instead of returning False as the docstring says for a file that does not parse. |  |

## By design (1)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/commands.py:repo_path` k=1 | The drive-letter check re.match(r'^[A-Za-z]:') rejects any repository path whose first component is a single letter followed by a colon (e.g. 'a:b'), although that is a valid git path inside the repository. |  | claude-sonnet-5-5: intended, claude-opus-5-5: None | `UsageError` |  |  |

## Mixed (2)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/commands.py:cmd_init` k=1 | cmd_init normalizes --paths with repo_path but does not remove duplicates, so `pkg` and `./pkg/` both become `pkg` and audit.json stores the path twice (and git archive gets it twice). |  | claude-sonnet-5-5: unclear, claude-opus-5-5: None | `['pkg', 'pkg']` | Passing the same folder in two spellings stores it twice in audit.json and passes it twice to git archive, which tolerates it, so the effect is cosmetic. |  |
| `tool/hpflow/fixcheck.py:check` k=2 | A repro that raises an error or times out after the fix is not flagged, because the comparison only happens when got['ok'] is true. A crashing repro is accepted as 'different from the result before the fix'. |  | claude-sonnet-5-5: real, claude-opus-5-5: unclear | `'accept'` | A repro that raises or times out after the fix gives no result, but check() only compares when ok is true, so a fix that makes the repro crash is accepted as giving a different result. | project/tool/hpflow/commands.py:778 |
