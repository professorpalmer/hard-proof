## Review packet for #305 (ten-minute read)

**Update (head `de4cafff`):** the owner chose the path rule for rows 1 and 2. Commit `de4cafff` puts event paths in repo root form and compares exact paths. Rows 1 and 2 are now `ok to merge`, with one open point for the owner (see "Open owner decision").

Reviewer: a Claude Code session, first on head `c4eaee33`. I read each fix commit against its bug record in `confirmed_bugs.json`. For each bug I checked four things: the fix is at the cause, the change is minimal, the change for inputs that the bug does not cover, and the new test fails on the old code.

**Count:** 21 bugs. 21 `ok to merge`, 0 `reverted`. 1 open owner decision (on rows 1 and 2).

**Proof that the tests catch the bugs:** I ran the 15 new test files against the `origin/dev` source (the new tests copied into an export of `dev`). 42 tests fail and 43 pass. Each of the 21 bugs has at least one test that fails on `dev`. The tests that pass on `dev` are guard tests for inputs that must not change.

### Bugs

Rows with an owner point come first.

| # | File | Function | What went wrong | Fix | Verdict | Severity (two verifiers) |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `puppetmaster/gates.py` (code in `worker_attribution.py`) | `_gate_write_scope` | A worker that names only the root `README.md` is charged for a pre-dirty `docs/README.md` that another writer changed, because `_same_path` matches by suffix. | `de4cafff`: `RepoFrame.canonical` puts each event path in repo root form when it is recorded (join to the worker cwd, remove `.` and `..`, relative to the git top level, absolute when outside). The gate compares exact paths. `_same_path` is deleted. The first fix (`3cd162f0`, reverted in `c4eaee33`) broke workers in a repo subdirectory; a test now covers that case. | ok to merge (see the open owner decision) | medium / low |
| 2 | `puppetmaster/gates.py` (code in `worker_attribution.py`) | `_gate_write_scope` | A dirty root `README.md` excuses a new out-of-scope `docs/README.md` that the run wrote, so the gate passes a stray write. | Same commit as row 1. `path_was_dirty_before` keeps the rule for an untracked directory, with exact equality in place of `_same_path`. | ok to merge (see the open owner decision) | high / medium |
| 3 | `puppetmaster/acceptance_criteria.py` | `criterion_status_records` | A worker that echoes a criterion with its `- ` or `1. ` marker gets no match, and its result is lost as `unknown`. | `_normalize_reported_criterion` runs the reported key through `normalize_acceptance_criteria` (same marker strip and length cut as the criteria). | ok to merge | medium / low |
| 4 | `puppetmaster/cli/helpers.py` | `routing_payload_from_args` | `--allowed-models ""` (or MCP `allowed_model_ids: []`) drops the allowlist, so the router can pick any model. | The flag presence (not its blank-filtered values) sets `allowed_model_ids`, and MCP forwards an empty list as `--allowed-models ""`. Matches `docs/FEATURES.md:149` "empty allowlists fail closed". Note: a script that passes an empty variable to `--allowed-models` now fails closed. | ok to merge | medium / low |
| 5 | `puppetmaster/dashboard.py` | `bind_dashboard_server` | `puppetmaster dashboard --host ::1` fails with `gaierror`, because the server class is IPv4 only. | The server class uses `AF_INET6` when the host contains `:`. | ok to merge | low / low |
| 6 | `puppetmaster/dashboard.py` | `bind_dashboard_server` | At the 65535 ceiling, the error names ports that were never tried. | The message names the last port tried. | ok to merge | low / low |
| 7 | `puppetmaster/diagnostics.py` (also `cursor_sdk_home.py`) | `_find_cursor_sdk_install` | A partial `@cursor/sdk` directory from an interrupted npm install counts as installed, so the bootstrap never repairs it. | A candidate counts only when it holds `package.json` (also in `_sdk_beside` and `home_sdk`). | ok to merge | medium / low |
| 8 | `puppetmaster/failure.py` | `classify_adapter_failure` | `status code 401.` at the end of a sentence gives `unknown`, not `not_authenticated`. | Lookahead `(?!\w\|\.\d)`: a dot after 401 is rejected only when a digit follows. | ok to merge | low / low |
| 9 | `puppetmaster/metr_seams.py` | `is_coordination_protocol_payload` | Role `mailbox-protocol` is not detected, because `PROTOCOL_ROLES` stores `mailbox_protocol`. | Try the role with both separators. | ok to merge | low / low |
| 10 | `puppetmaster/orchestrator.py` | `Orchestrator._recoverable_failure_by_task` | After an auto-fallback re-queue, a stale `auth` failure of the first attempt keeps a hard failure of the new attempt classed as recoverable. | For a task with `fallback_attempts` N > 0, only failures after the `router-fallback` artifact with `fallback_attempt` N count. Note: with N > 0 and no such marker, no failure counts (fail closed). | ok to merge | medium / medium |
| 11 | `puppetmaster/preflight.py` | `adapter_cli_present` | `CLAUDE_CODE_COMMAND='npx -y @anthropic-ai/claude-code'` reads as "not installed", so routing drops claude-code. | Split with `command_parts` and resolve only the first word, as the adapters do. | ok to merge | medium / medium |
| 12 | `puppetmaster/rate_limit_headers.py` | `parse_rate_limit_headers` | An Anthropic RFC 3339 reset gives `reset_at=None`, so an exhausted window does not block. | `reset_at` tries `datetime.fromisoformat` (with `Z` to `+00:00` for Python 3.9) before RFC 2822. A naive time is read as UTC. | ok to merge | medium / medium |
| 13 | `puppetmaster/savings.py` | `collect_routing_records` | Two fallbacks of one task count as 2 tasks, so `fallback_rate` can be 2.0. | Count each (kind, job, task) once. | ok to merge | medium / low |
| 14 | `puppetmaster/savings.py` | `collect_routing_records` | Two escalations of one task count as 2 tasks, so `escalation_rate` can be above 1.0. | Same change as row 13. | ok to merge | low / low |
| 15 | `puppetmaster/store.py` (also `sqlite_store.py`) | `SwarmStore.retrieve_memory` | A goal word with punctuation (`zebra,`) never matches the stored word, so relevant memory is not injected. | Query terms come from `re.findall(r"\w+", ...)` in both stores. Note: a hyphen or dot also splits a term now (`file.py` gives `file`), so some scores change. | ok to merge | medium / medium |
| 16 | `puppetmaster/worker_resume.py` | `_resolve` | A newer receipt without a session id (a failed repair attempt) hides an older receipt with one, so `resume_from` runs fresh. | Pick the newest receipt that has a session id, as `repair_resume_record` does. The ephemeral check stays on the chosen receipt. | ok to merge | low / low |
| 17 | `puppetmaster/write_intent.py` | `adapter_may_write` | `antigravity --mode analyze` (run as `agy --mode plan`) takes an exclusive edit claim on its whole scope. | Use the adapter's own `resolve_antigravity_mode`. Note: an unknown mode or upper-case `PLAN` now follows the adapter map too. | ok to merge | medium / medium |
| 18 | `puppetmaster/adapters/cursor.py` | `cursor_artifact_from_item` | A `null` evidence entry is stored as the text `None`. | `_string_list` skips `None`. | ok to merge | low / low |
| 19 | `puppetmaster/adapters/cursor.py` | `cursor_artifact_from_item` | A `NaN` confidence gives 0.0, not the 0.75 default. | `_confidence` returns 0.75 for a value that is not finite. Note: `Infinity` also gives 0.75 now (was 1.0). | ok to merge | low / low |
| 20 | `puppetmaster/adapters/cursor.py` | `cursor_artifact_from_item` | A wrapped Codex item with an empty inner `type` is dropped. | `wrapped.get("type") or wrapped_type`. | ok to merge | low / low |
| 21 | `puppetmaster/adapters/cursor.py` | `CursorAdapter.run` | Prose with a citation such as `[1]` before the JSON makes `_json_prefix_decode` return `[1]`, so all findings are lost. | `_json_prefix_decode` skips a list that holds no object. Note: a bare `[]` before a trailer now gives `None`; both give no artifacts and the same degraded result. | ok to merge | medium / medium |

### Open owner decision (rows 1 and 2)

The owner rule says: path arithmetic only, no realpath. With arithmetic only, the existing test `tests/test_parity_agentic.py::AttributionTests::test_absolute_path_is_repo_relative` fails on macOS. The event path is `/var/folders/.../abs.py` and the resolved worker cwd is `/private/var/folders/...`, so a real worker edit becomes "unnamed", and an unnamed path that was dirty at the start is excused (the false-pass direction).

`de4cafff` adds one step: an absolute path that falls outside the top level is tried again with its nearest existing folder resolved. The file itself is never resolved, so an absent file still works (test `test_linked_folder_above_an_absent_file`). **Decision:** keep this step, or remove it and accept that a path through a linked folder does not match.

Notes on the path rule:
- Fail closed when no cwd is known: this cannot occur at capture. The codex, claude-code and agentic adapters all record paths with `Path(task.payload.get("cwd") or ".").resolve()`.
- The top level is the nearest folder with a `.git` entry (no subprocess). It differs from `git rev-parse --show-toplevel` only when `GIT_DIR` or `GIT_WORK_TREE` is set.
- A receipt written by the old code keeps cwd-relative paths. This matters only for a run that is in flight during the upgrade.
- Tests in `tests/test_hpfix_puppetmaster_gates.py` (17): both bug repros in both directions, a worker in `<repo>/pkg` that edits `pkg/x.py` with reference `x.py`, absolute paths, `./` and `..`, a path outside the repository, Windows separators, a linked folder, and a property test that two different canonical paths never match. On `dev`, the 4 bug tests fail by assertion. The other new tests fail there too, because `RepoFrame` does not exist on `dev`.

### CI state

Head `de4cafff`: all 18 checks pass (CI runs 44401492077 pull_request and 44401486499 push, Windows store canary 44401492081 and 44401486432). Before that, head `c4eaee33` passed in runs 44374358387 and 44374348012.

| Platform | Result |
| --- | --- |
| Linux, Python 3.9 (`test (ubuntu-latest, 3.9)`) | pass |
| Linux, Python 3.12 | pass |
| macOS, Python 3.12 | pass |
| Windows, shards 1-4 | pass |
| `windows-store` canary | pass |
| `reuse-green-tree` | pass |

One failure on the earlier head `906aedf0` was a flake (case d, not related): macOS `test_stop_receipt.StopReceiptTests.test_a_cut_running_worker_records_a_stop_receipt_and_settles` gave `ReadUnavailable: unable to open database: source changed` in `readonly.py` (run 44372115986). No fix touches `readonly.py`, `projections.py` or `cut_task`. A rerun of that job on the same SHA passed (job 135049333495), and the job passes on the new head.

Locally (macOS, Python 3.14, under the shared test lock): the 14 new test files plus `test_readonly_diff_attribution.py` and `test_nongit_write_scope.py` give 95 passed.

### Repository tests that this branch changes

| Test | Change | Reason |
| --- | --- | --- |
| `tests/test_puppetmaster.py`, three tests near lines 8631, 8659, 8675 (cursor SDK discovery) | Each fixture now writes `package.json` into the fake `node_modules/@cursor/sdk` directory. No assertion changed. | Fix 7 counts an SDK only when it holds `package.json`. An empty directory was the fixture for "installed", and it is now the case that the bug is about. |

No other existing test changed. The new tests are in `tests/test_hpfix_*.py` (15 files, 95 tests).

### Commits that this review added

- `c4eaee33` Revert the gates.py fix: it breaks workers in a repo subdirectory.
- `de4cafff` Compare write_scope paths in repo root form, not by suffix (rows 1 and 2, the owner's rule plus the linked-folder step).
