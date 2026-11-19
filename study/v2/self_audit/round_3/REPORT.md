# hpflow audit of hard-proof-repo at bc1f34aa0a58

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 7.

## Confirmed (7)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/codexhome.py:lean_config` k=1 | A bracket inside a string value of a dropped table (e.g. command = "foo[") is counted as an open array, so lean_config swallows the following lines, including the kept [profiles.p] table. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'model="x"\n'` | A '[' inside a string value in a dropped table (e.g. an mcp_servers command or args entry) leaves skip_depth positive, so every following line, including kept tables like [profiles.p], is silently dropped from the worker's lean config.toml. | project/tool/hpflow/codexhome.py:150 |
| `tool/hpflow/commands.py:fix_graph` k=1 | The flow id built in fix_graph does not include the bug ids of the group, although the task text differs. Two fix runs of the same file with different bugs (e.g. --only) get the same graph id. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `True` | Two fix runs of the same file with different bug sets (cmd_fix --only) get the same graph id, so the second run overwrites the stored graph file <id>.json and the first run's record['graph'] then points to a graph whose task text lists other bugs. | project/tool/hpflow/commands.py:864 |
| `tool/hpflow/commands.py:cmd_init` k=1 | An explicit path such as './pkg' passes the presence check (git resolves it) but is stored unnormalized, so in_paths and the git diff pathspecs never match 'pkg/...' files; only trailing slashes are cleaned. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `['./pkg']` | A user passing --paths ./pkg gets './pkg' stored in audit.json, so in_paths never matches 'pkg/...' files and changed-function targets are silently dropped. | project/tool/hpflow/cli.py:150 |
| `tool/hpflow/commands.py:cmd_init` k=2 | import_root './src' is only stripped of slashes, so it is stored as './src' and the package path becomes './src/pkg'; top_of and run_snippet then misbehave. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `('./src', ['./src/pkg'])` | A user passing --import-root ./src gets './src' stored, so top_of never strips the root (file names are 'src/...') and package paths become './src/pkg', giving wrong top names and snippets. | project/tool/hpflow/cli.py:150 |
| `tool/hpflow/commands.py:parse_diff` k=1 | git writes a trailing tab after a path that contains a space in the ---/+++ header lines. parse_diff keeps the tab in the path, so the file cannot be found. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `('my file.py\t', 'my file.py\t')` | A changed .py file whose path contains a space gets a trailing tab in its path, so in_paths/git show fail and the changed functions of that file are silently not targeted. | project/tool/hpflow/commands.py:335 |
| `tool/hpflow/commands.py:parse_diff` k=2 | git quotes paths with non-ASCII characters in the ---/+++ headers, as "a/\303\251.py". parse_diff strips two characters and leaves a stray quote, giving a wrong path. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `('/\\303\\251.py"', '/\\303\\251.py"')` | With git's default core.quotepath, a changed file with a non-ASCII name appears as a quoted octal path, which parse_diff turns into a garbage path (stray quote, no a/ strip), so that file is skipped by cmd_targets --changed. | project/tool/hpflow/commands.py:335 |
| `tool/hpflow/fixcheck.py:check` k=1 | The search for related tests misses a test file that imports the changed module with a top-level `from mod import x` (no dot, module not in the file name), so its failing tests are never run and the fix is accepted. |  | claude-sonnet-5-5: real, claude-opus-5-5: real | `'accept'` | A repository test file that does `from mod import f` (flat layout, module not in file name) is not selected as related, so a fix that breaks it is accepted instead of rejected. | project/tool/hpflow/commands.py:867 |

## Real but not reachable (0)

None.

## By design (0)

None.

## Mixed (1)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/commands.py:cmd_fix` k=1 | The slug (worktree, branch, test file name) of a file depends on which bugs are selected: with `only`, the twin file is filtered out before the plain-slug collision check, so pkg/a_b.py gets the plain slug `pkg-a-b` with only=[b0] but `pkg-a-b-<digest>` in the full run. The same file gets different  |  | claude-sonnet-5-5: unclear, claude-opus-5-5: None | `(['pkg-a-b-95281638'], ['pkg-a-b'])` | With --only, a file whose twin is filtered out gets the plain slug, so the same file gets a different worktree, branch and test file name than in a full run; no collision happens inside either run. | project/tool/hpflow/cli.py:161 |
