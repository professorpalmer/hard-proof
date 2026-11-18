## Review packet for #699 (update 2: owner rules applied)

Status: draft. Do not merge before the owner reads the open decision below the table.

Summary: 24 bugs. 23 are `ok to merge` (2 of them with rules that the owner set). 1 is `accepted by the owner` with no code change. No fix adds a raise on a path that must not raise. One owner decision is open (see below the table).

How I checked each fix:

1. I read each diff against its record in `confirmed_bugs.json`.
2. I ran the 10 new test files against `origin/dev`. Each of the 21 kept bugs has at least one new test that fails there (39 failed, 29 passed).
3. I probed old and new code with inputs that the bug does not cover. The notes column gives each change in behavior that I found.

### Bugs

Rows with an owner rule come first.

| Bug | File | Function | What went wrong | Fix | Verdict | Severity (two verifiers) |
| --- | --- | --- | --- | --- | --- | --- |
| 1af9b7d4-2 | `harness/pilot_guards.py` | `is_explicit_swarm_user_message` | "Please do not use agentic workers" gets the explicit swarm policy and a stored swarm mandate. | Owner rule (`90010b16`): a refusal is a negation (do not, don't, dont, never, no need to, without), a launch verb (use, launch, start, run, dispatch, spawn, spin up, fan out), at most two words from a closed list (a, an, any, the, more, agentic, extra, additional, parallel), then workers, swarm, agents or subagents. | ok to merge. My first review reverted a wider fix (`cda67849`). The owner rule keeps each counter-example: "Use a swarm to audit auth. Do not run more than three workers" and "Run a swarm over auth, do not use the old swarm results" stay explicit. | high / high |
| 1af9b7d4-5 | `harness/pilot_guards.py` | `is_explicit_swarm_user_message` | "Launch a swarm to find where is the auth token validated" gets the solo note. | Owner rule (`90010b16`): a launch verb, an optional a, an, the, another or one, then "swarm" wins over a narrow phrase in the same clause. | ok to merge. "Where is the code we run when the swarm finishes?" stays solo (the reverted fix made it explicit). | medium / medium |
| 791b83f9-7 | `harness/pilot_guards.py` | `is_broad_intent_user_message` | "browser windows on my Mac" reads as a Windows-vs-Mac contrast, so the pilot gets the broad-intent note. | No code change. | **accepted by the owner**: low severity, and each tighter rule lost real comparisons ("Why does the build fail on Linux but not Windows?", "Does this work on Mac and Windows?"). The golden table records the result. | low / low |
| 1af9b7d4-1 | `harness/pilot_guards.py` | `is_explicit_swarm_user_message` | A launch request plus a separate "where is" question gets the solo note. | The narrow veto applies per clause (now in `_delegation_signals`), not to the whole message. | ok to merge | medium / medium |
| 1af9b7d4-3 | `harness/pilot_guards.py` | `is_explicit_swarm_user_message` | "Don’t swarm the repo" with U+2019 gets the explicit swarm policy and a mandate. | The two refusal patterns accept `'` or `’`. | ok to merge | medium / high |
| e3af4031-2 | `harness/pilot_guards.py` | `normalize_action_args` | A second `search_files` in a different `paths` scope gets a cached replay of the first scope. | The key holds `path`/`paths` (sorted) and `glob`, `case_insensitive`, `context_lines`, `files_only`, the same fields that `_do_search_files` reads. Keys for calls without these fields do not change. | ok to merge | medium / medium |
| e3af4031-5 | `harness/pilot_guards.py` | `normalize_action_args` | Two `edit_file` calls that differ only in whitespace share one key, so the second edit is not applied. | The key holds a SHA-256 of the exact `old_str` and `new_str`. | ok to merge | high / medium |
| 791b83f9-1 | `harness/pilot_guards.py` | `is_broad_intent_user_message` | "everywhere is" matches the narrow veto inside the word. | Each narrow alternative starts with `\b`. | ok to merge | low / low |
| 791b83f9-2 | `harness/pilot_guards.py` | `is_broad_intent_user_message` | "bitmap the" matches the broad pattern inside the word. | The pattern is `\bmap\s+the\b`. | ok to merge | low / low |
| 67cd0a74-1 | `harness/providers.py` | `build_pilot` | `deepseek/deepseek-r1:free` sends the model "free" to OpenRouter. | An unknown prefix before ":" stays part of the model name. | ok to merge. Note: a typo prefix such as `antropic:claude-opus-5-5` now goes to OpenRouter as the full string. Before, the prefix was dropped and the bare model resolved to Anthropic. | medium / medium |
| 146de2cf-6 | `harness/runaway_guard.py` | `observe_step` | Waits on different jobs with the same generic body give the "same work target" steer. | The progress key holds the polled action key. | ok to merge. Note: a wait with other arguments on the same job also starts the count again. The poll count already works this way. | low / low |
| a48b7e17-1 | `harness/context_budget.py` | `maybe_persist_result` | A head-only preview whose text holds "... [omitted" gets the label "head and tail". | `maybe_persist_result` passes the real preview shape. The text guess stays only as the default for other callers. | ok to merge | low / low |
| d349963d-1 | `harness/api/codegraph_index.py` | `maybe_refresh_codegraph` | An edit of a .lua, .c, .cpp or .rb file does not mark the index stale. | `codegraph_is_stale` uses `codegraph_preflight.INDEXABLE_EXTENSIONS`, the list of the indexer. | ok to merge | medium / medium |
| 6e747ee7-1 | `harness/browser_real_profile.py` | `is_live_browser_user_data_dir` | With both XDG and snap Chrome on Linux, the snap profile passes the live-profile guard. | The guard checks every Linux candidate (XDG, snap, flatpak). `real_profile_data_dir` still returns the first one that exists. | ok to merge | medium / medium |
| 81081b2d-1 | `harness/skill_store.py` | `Skill.slug` | A slug cut at 48 characters can end in "-", and save then overwrites another skill. | `_slug` strips "-" after the cut, so `_slug` is idempotent. | ok to merge | medium / low |
| f75dc534-1 | `harness/skill_store.py` | `SkillStore.propose_update` | A distiller patch for "Deploy" overwrites a user skill "Deploy patch". | `propose_update` raises `ValueError` when the patch slug holds a skill that is not a patch of the same root. | ok to merge. The raise is not on the chat hot path: the only caller is `distill_session`, and `WikiDistillMixin.distill` catches it (`harness/wiki_distill.py:362-369`) and returns status "error". | medium / medium |
| f75dc534-2 | `harness/skill_store.py` | `SkillStore.propose_update` | Approval of a renamed patch leaves the old active skill, so two skills exist. | `set_state` removes the old file when the new name moves the slug. | ok to merge | medium / medium |
| 8c8070c4-1 | `harness/worker.py` | `_detect_escaped_writes` | `cp a.txt sub/dir/b.txt` reports an escaped write to `/dir/b.txt`. | The destination is the last operand (or `-t DIR`), split with `shlex`, and counts only when the operand itself is absolute. | ok to merge (see the note below the table) | medium / medium |
| 8c8070c4-2 | `harness/worker.py` | `_detect_escaped_writes` | `cp /etc/hosts ./hosts.txt` reports the source as an escaped write. | Same change as 8c8070c4-1. | ok to merge | medium / medium |
| 8c8070c4-4 | `harness/worker.py` | `_detect_escaped_writes` | `ls /opt/install/bin` reports `/bin`. | A command word next to "/" is a path component, not a command. | ok to merge | low / medium |
| 8c8070c4-5 | `harness/worker.py` | `_detect_escaped_writes` | `pip install /tmp/pkg.whl` reports the package path as a write. | `install` after a package manager word (pip, npm, apt, brew and others) is skipped. | ok to merge | medium / medium |
| 67ffe9e8-1 | `pmharness/drivers/cursor_cli.py` | `_tool_hint_payload` | A generic tool name such as "tool" paints the "tool tool" row. | When `humanize_cursor_tool_name` gives no kind, the kind is "tool_call". That occurs only for an empty or generic name. | ok to merge | low / low |
| 11691ae0-1 | `pmharness/intent.py` | `infer_roles` | "review" inside "previewer" starts five paid workers. | Each broad signal must start at a word start. | ok to merge. Note: "Debug the login timeout" and "Upscale the images" now get one explorer, not five workers. | medium / low |
| 11691ae0-2 | `pmharness/intent.py` | `infer_roles` | "data-flow" or "control-flow" gets no pipeline-mapper. | `_FLOW_SIGNALS` adds the hyphenated forms. | ok to merge | low / low |

Note on `worker.py`: these commands are no longer flagged: `cp a ~/x`, `cp a $HOME/x`, `make install PREFIX=/usr/local`. The old code flagged them only through the fault of 8c8070c4-1, and it named the wrong path (`/x`, `/usr/local`). The redirect, tee and mkdir rules do not handle `~` either. One real escape is now caught that the old code missed: `cp a /abs/b 2>/dev/null` (the old code took `/dev/null` as the destination).

### Policy order

`harness/pilot_guards.py` has one pure function for the order of the swarm policy: `swarm_policy_table(refusal, launch, narrow, broad)`. It returns `solo` for a refusal, else `explicit` for a launch, else `solo` for a narrow question, else `broad` for a broad request, else `solo`. `swarm_policy_for_message`, `is_explicit_swarm_user_message` and `_is_delegation_opt_out_user_message` use it. `_delegation_signals` computes `refusal` and `launch` for each clause.

Golden table: `test_swarm_policy_golden_table` in `tests/test_hpfix_harness_pilot_guards.py` (21 sentences) and `test_swarm_policy_table_order` (all 16 input rows). On `origin/dev` the bug sentences fail (9 rows) and each counter-example passes (12 rows).

### Open owner decision

"A refusal always wins" is applied inside the table. Between clauses, the last delegation clause still wins, as before:

- "Do not use workers for this part, but use a swarm for the audit." stays `explicit`.
- "Use a swarm to audit everything. Actually, do not use the swarm" is `solo`.

The old test `test_mixed_delegation_contrast_honors_positive_swarm_clause` (commit `87cdb7a3`, 2026-09-27, "honor explicit worker opt-outs and later corrections") asks for the first result. I did not change that test. **Decision:** must a refusal in any clause also win over a later launch? If yes, that old test changes, and `_delegation_signals` sets `refusal` for any clause.

Counts: 23 ok to merge, 1 accepted by the owner (no code change), 0 reverted. Open decisions: 1 (above).

### CI

`tests.yml` runs only on pull requests to `main`, so this pull request shows no checks. I started `tests-full` by hand (workflow_dispatch) on the head `90010b16`: run 44401212115. That run has the same matrix as the nightly run on `main`, with the fix of #701 (3.9 leg on `ubuntu-24.04`).

| Job | Result |
| --- | --- |
| pytest (ubuntu-24.04, 3.9) | passed |
| pytest (ubuntu-latest, 3.11) | passed |
| pytest (macos-latest, 3.11) | passed |
| pytest (windows-latest, 3.9) | passed |
| pytest (windows-latest, 3.11) | passed |
| frontend-build | passed |

All 6 jobs are green. The earlier run 44373762567 (head `cda67849`) had two red jobs, and both were failures on `main` that #701 fixes.

Local check on macOS (`-n 0`, through the shared lock): the 26 test files that touch the swarm policy, 802 passed, 1 skipped.

### Tests that I changed

- `tests/test_hpfix_harness_pilot_guards.py` (new in this pull request): `cda67849` removed the tests of the three reverted fixes. `90010b16` adds the golden table and the 16-row table test.
- No test file that exists on `dev` is changed by this pull request.

### Commits that I added

- `49628b0f` Merge `origin/dev` (v0.9.683 pin change) into the branch.
- `cda67849` Revert 3 of the 9 `pilot_guards.py` fixes for owner review.
- `104004c4` Merge `origin/dev` (v0.9.684, with the nightly fix #701) into the branch.
- `90010b16` Apply the owner rules for 1af9b7d4-2 and 1af9b7d4-5 (`swarm_policy_table`).
