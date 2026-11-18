## Review packet for #306 (ten-minute read)

Reviewer: a Claude Code session. Source: the audit of the functions that changed between v1.50.0 and v1.51.1 (`~/Projects/hp-work/audit-pm-1510/confirmed.json`). The fixes came as uncommitted diffs in four fix worktrees. I applied them on `fix/audit-release-diff` (cut from `origin/dev` `7da211ad`) and read each one again: the fix is at the cause, the change is minimal, the change for inputs that the bug does not cover, and the new test fails on `dev`.

**Count:** 7 bugs. 7 `ok to merge`, 0 `reverted`, 0 open owner decisions. I changed one fix (row 5): I moved its catch to the cause.

**Proof that the tests catch the bugs:** I copied the 4 new test files into an export of `dev`. 19 tests fail and 13 guard tests pass. Each of the 7 bugs has at least one failing test.

**What I changed in the worker fixes:**
- Two fix worktrees (`registry-sync` and `routing-authority`) had the same change to `registry_sync.unroutable_pin_hint` for two records with one cause (rows 3 and 4). I applied it once.
- Row 5: the worker caught `UnicodeDecodeError` and `OSError` in the doctor check. The cause is `model_registry.load_registry`, which turns bad JSON into `RuntimeError` but let a decode error escape. I moved the catch there. Now `models sync` and the MCP model tools give a clean error too. Every caller of `load_registry` that catches an error catches `RuntimeError` or a wider class.

### Bugs

| # | File | Function | What went wrong | Fix | Verdict | Severity |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `puppetmaster/routing_authority.py` | `validate_pinned_dispatch` | An agentic pin on a Codex `-pro` registry wire name (`gpt-5.6-sol-pro`) binds, but binding hardens the payload to the base id, and every worker then fails at dispatch with "executable model and pinned wire identity diverge". | When `codex_pro_remapped_from` equals the registry wire name, compare against the remapped base id. Other pins are compared as before; a diverged wire still fails (test). | ok to merge | medium |
| 2 | `puppetmaster/diagnostics.py` | CLI install checks (`run_doctor`) | `Path(first).exists()` on a bare command name tests the current folder, so a folder named `claude` or `codex` makes doctor (and `adapter_is_available`) report the CLI as installed. | Path test only for a command with a path separator or a leading `~`; a bare name goes to `shutil.which`. Same change for claude, codex, hermes, fx, antigravity. Note: on Windows `shutil.which` also searches the current folder (Python documentation, recalled, not probed on Windows), as Windows process start does, so no real case is lost there. | ok to merge | medium |
| 3 | `puppetmaster/registry_sync.py` | `unroutable_pin_hint` | When the starter model is in the registry under another, disabled id, the hint says "run `models sync --apply`", but sync counts that starter id as covered and adds nothing. | When no entry has the starter id, find the entry with the same execution identity (the test `plan_starter_sync` uses) and report its disabled or retired state with the enable command. Note: when that covering entry is enabled, the hint is now empty and the caller says "it may be disabled, retired, or absent" (before: the sync advice, which could not help). | ok to merge | low |
| 4 | `puppetmaster/routing_authority.py` | `_pin_failure_detail` | Same cause as row 3: it calls `unroutable_pin_hint`. | Same commit as row 3. | ok to merge | low |
| 5 | `puppetmaster/model_registry.py` (record: `diagnostics.py`) | `_registry_starter_sync_check` | A registry file that is not UTF-8 makes doctor show the row as a crash (`check raised: UnicodeDecodeError`), not the documented "registry unreadable" warning. | `load_registry` raises `RuntimeError("... is not UTF-8")` (moved from the doctor check to the cause, see above). | ok to merge | low |
| 6 | `puppetmaster/diagnostics.py` | `_agent_rules_check` (`run_doctor`) | A string prefix test on HOME, then `relative_to`: for home `/x/a` and a project in `/x/ab`, `relative_to` raises and the agent-rules row is an error. | `Path.is_relative_to` (Python 3.9+). | ok to merge | low |
| 7 | `puppetmaster/codegraph.py` | `ensure_codegraph_provisioned` | `PUPPETMASTER_CODEGRAPH_PROVISION_TIMEOUT_SECONDS=inf` makes `int(float(raw))` raise `OverflowError` from a function that must never raise. | Also catch `OverflowError`; the timeout falls back to 300 s. | ok to merge | low |

### CI state

Head `e965b600`: all 18 checks pass (CI runs 44404381583 pull_request and 44404362761 push, Windows store canary 44404381203 and 44404362585): Linux 3.9 and 3.12, macOS 3.12, Windows shards 1-4, `windows-store`, `reuse-green-tree`.

The first head `04762936` failed on Windows shards 1 and 3 (run 44402018421), in two new diagnostics tests only (case c, not portable). `test_bare_name_on_path_still_counts` made a file without an extension and set `PATHEXT` to empty, so Windows `shutil.which` could not find it. `test_explicit_relative_path_still_counts` built `.\zzcli`, and the POSIX `shlex.split` in the check removed the backslash. The fixes did not change. Commit `e965b600` changes only those two tests.

Locally (macOS, under the shared test lock): the 4 new test files plus `test_registry_sync.py`, `test_routing_authority_isolation.py`, `test_recovery_pin_governance.py`, `test_codegraph_process_group.py`, `test_codegraph_warm.py`, `test_hook_interpreter_doctor.py`, `test_fx_adapter.py`, `test_antigravity_adapter.py`, `test_billing_provenance.py` and `test_setup_readiness.py` pass.

### Repository tests that this branch changes

No existing test changed. New tests: `tests/test_hpfix_puppetmaster_codegraph.py`, `_diagnostics.py`, `_registry_sync.py`, `_routing_authority.py`. The diagnostics test file covers rows 2, 5 and 6, and it is in the `model_registry.py` commit.

### Follow-up seen in passing (not fixed here)

The diagnostics install checks split a configured command with POSIX `shlex.split`. On Windows that removes each backslash, so `CLAUDE_CODE_COMMAND=C:\tools\claude.exe` becomes `C:toolsclaude.exe` and reads as not installed. The adapters use `command_parts`, which splits in non-POSIX mode on Windows. This is on `dev` too.

### Commits on this branch

- `04da8be9` Fix 1 bug in puppetmaster/codegraph.py (row 7)
- `b206e593` Fix 2 bugs in puppetmaster/diagnostics.py (rows 2 and 6)
- `377eef7e` Fix 1 bug in puppetmaster/model_registry.py (row 5)
- `d078e610` Fix 2 bugs in puppetmaster/registry_sync.py (rows 3 and 4)
- `04762936` Fix 1 bug in puppetmaster/routing_authority.py (row 1)
- `e965b600` Make the diagnostics install-check tests portable to Windows (test-only, case c)
