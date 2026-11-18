## v1.51.2 — 2026-11-18

**28 bug fixes from an audit of small functions.**
An agent review looked at one function at a time and gave a runnable repro for
each finding. A finding became a fix only after these steps: the repro still
gave the wrong result on `dev`, two verifier agents on different models each
named a caller that reaches it, a fix worker wrote the smallest change and a
regression test, a judge reviewed the diff, and a second review ran the new
tests against the old code. Each bug has a test in `tests/test_hpfix_*.py`.

- `_gate_write_scope` in `puppetmaster/gates.py` (code in
  `worker_attribution.py`): A worker that names only the root `README.md` is
  charged for a pre-dirty `docs/README.md` that another writer changed,
  because `_same_path` matches by suffix. `RepoFrame.canonical` puts each
  event path in repo root form when it is recorded (join to the worker cwd,
  remove `.` and `..`, relative to the git top level, absolute when outside).
  The gate compares exact paths. `_same_path` is deleted.
- `_gate_write_scope` in `puppetmaster/gates.py` (code in
  `worker_attribution.py`): A dirty root `README.md` excuses a new
  out-of-scope `docs/README.md` that the run wrote, so the gate passes a stray
  write.
- `criterion_status_records` in `puppetmaster/acceptance_criteria.py`: A
  worker that echoes a criterion with its `- ` or `1. ` marker gets no match,
  and its result is lost as `unknown`. `_normalize_reported_criterion` runs
  the reported key through `normalize_acceptance_criteria` (same marker strip
  and length cut as the criteria).
- `routing_payload_from_args` in `puppetmaster/cli/helpers.py`:
  `--allowed-models ""` (or MCP `allowed_model_ids: []`) drops the allowlist,
  so the router can pick any model. The flag presence (not its blank-filtered
  values) sets `allowed_model_ids`, and MCP forwards an empty list as
  `--allowed-models ""`. Matches `docs/FEATURES.md:149` "empty allowlists fail
  closed".
- `bind_dashboard_server` in `puppetmaster/dashboard.py`: `puppetmaster
  dashboard --host ::1` fails with `gaierror`, because the server class is
  IPv4 only. The server class uses `AF_INET6` when the host contains `:`.
- `bind_dashboard_server` in `puppetmaster/dashboard.py`: At the 65535
  ceiling, the error names ports that were never tried. The message names the
  last port tried.
- `_find_cursor_sdk_install` in `puppetmaster/diagnostics.py` (also
  `cursor_sdk_home.py`): A partial `@cursor/sdk` directory from an interrupted
  npm install counts as installed, so the bootstrap never repairs it. A
  candidate counts only when it holds `package.json` (also in `_sdk_beside`
  and `home_sdk`).
- `classify_adapter_failure` in `puppetmaster/failure.py`: `status code 401.`
  at the end of a sentence gives `unknown`, not `not_authenticated`. Lookahead
  `(?!\w\
- `is_coordination_protocol_payload` in `puppetmaster/metr_seams.py`: Role
  `mailbox-protocol` is not detected, because `PROTOCOL_ROLES` stores
  `mailbox_protocol`. Try the role with both separators.
- `Orchestrator._recoverable_failure_by_task` in
  `puppetmaster/orchestrator.py`: After an auto-fallback re-queue, a stale
  `auth` failure of the first attempt keeps a hard failure of the new attempt
  classed as recoverable. For a task with `fallback_attempts` N > 0, only
  failures after the `router-fallback` artifact with `fallback_attempt` N
  count.
- `adapter_cli_present` in `puppetmaster/preflight.py`:
  `CLAUDE_CODE_COMMAND='npx -y @anthropic-ai/claude-code'` reads as "not
  installed", so routing drops claude-code. Split with `command_parts` and
  resolve only the first word, as the adapters do.
- `parse_rate_limit_headers` in `puppetmaster/rate_limit_headers.py`: An
  Anthropic RFC 3339 reset gives `reset_at=None`, so an exhausted window does
  not block. `reset_at` tries `datetime.fromisoformat` (with `Z` to `+00:00`
  for Python 3.9) before RFC 2822. A naive time is read as UTC.
- `collect_routing_records` in `puppetmaster/savings.py`: Two fallbacks of one
  task count as 2 tasks, so `fallback_rate` can be 2.0. Count each (kind, job,
  task) once.
- `collect_routing_records` in `puppetmaster/savings.py`: Two escalations of
  one task count as 2 tasks, so `escalation_rate` can be above 1.0.
- `SwarmStore.retrieve_memory` in `puppetmaster/store.py` (also
  `sqlite_store.py`): A goal word with punctuation (`zebra,`) never matches
  the stored word, so relevant memory is not injected. Query terms come from
  `re.findall(r"\w+", ...)` in both stores.
- `_resolve` in `puppetmaster/worker_resume.py`: A newer receipt without a
  session id (a failed repair attempt) hides an older receipt with one, so
  `resume_from` runs fresh. Pick the newest receipt that has a session id, as
  `repair_resume_record` does. The ephemeral check stays on the chosen
  receipt.
- `adapter_may_write` in `puppetmaster/write_intent.py`: `antigravity --mode
  analyze` (run as `agy --mode plan`) takes an exclusive edit claim on its
  whole scope. Use the adapter's own `resolve_antigravity_mode`.
- `cursor_artifact_from_item` in `puppetmaster/adapters/cursor.py`: A `null`
  evidence entry is stored as the text `None`. `_string_list` skips `None`.
- `cursor_artifact_from_item` in `puppetmaster/adapters/cursor.py`: A `NaN`
  confidence gives 0.0, not the 0.75 default. `_confidence` returns 0.75 for a
  value that is not finite.
- `cursor_artifact_from_item` in `puppetmaster/adapters/cursor.py`: A wrapped
  Codex item with an empty inner `type` is dropped. `wrapped.get("type") or
  wrapped_type`.
- `CursorAdapter.run` in `puppetmaster/adapters/cursor.py`: Prose with a
  citation such as `[1]` before the JSON makes `_json_prefix_decode` return
  `[1]`, so all findings are lost. `_json_prefix_decode` skips a list that
  holds no object.
- `validate_pinned_dispatch` in `puppetmaster/routing_authority.py`: An
  agentic pin on a Codex `-pro` registry wire name (`gpt-5.6-sol-pro`) binds,
  but binding hardens the payload to the base id, and every worker then fails
  at dispatch with "executable model and pinned wire identity diverge". When
  `codex_pro_remapped_from` equals the registry wire name, compare against the
  remapped base id. Other pins are compared as before; a diverged wire still
  fails (test).
- CLI install checks (`run_doctor`) in `puppetmaster/diagnostics.py`:
  `Path(first).exists()` on a bare command name tests the current folder, so a
  folder named `claude` or `codex` makes doctor (and `adapter_is_available`)
  report the CLI as installed. Path test only for a command with a path
  separator or a leading `~`; a bare name goes to `shutil.which`. Same change
  for claude, codex, hermes, fx, antigravity.
- `unroutable_pin_hint` in `puppetmaster/registry_sync.py`: When the starter
  model is in the registry under another, disabled id, the hint says "run
  `models sync --apply`", but sync counts that starter id as covered and adds
  nothing. When no entry has the starter id, find the entry with the same
  execution identity (the test `plan_starter_sync` uses) and report its
  disabled or retired state with the enable command.
- `_pin_failure_detail` in `puppetmaster/routing_authority.py`: Same cause as
  row 3: it calls `unroutable_pin_hint`.
- `_registry_starter_sync_check` in `puppetmaster/model_registry.py` (record:
  `diagnostics.py`): A registry file that is not UTF-8 makes doctor show the
  row as a crash (`check raised: UnicodeDecodeError`), not the documented
  "registry unreadable" warning. `load_registry` raises `RuntimeError("... is
  not UTF-8")` (moved from the doctor check to the cause, see above).
- `_agent_rules_check` (`run_doctor`) in `puppetmaster/diagnostics.py`: A
  string prefix test on HOME, then `relative_to`: for home `/x/a` and a
  project in `/x/ab`, `relative_to` raises and the agent-rules row is an
  error. `Path.is_relative_to` (Python 3.9+).
- `ensure_codegraph_provisioned` in `puppetmaster/codegraph.py`:
  `PUPPETMASTER_CODEGRAPH_PROVISION_TIMEOUT_SECONDS=inf` makes
  `int(float(raw))` raise `OverflowError` from a function that must never
  raise. Also catch `OverflowError`; the timeout falls back to 300 s.

