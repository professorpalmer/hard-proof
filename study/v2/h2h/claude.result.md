The review of `main..feature` produced 10 findings, ranked below. Per the no-verify recipe, none were checked by running code. I tested two things directly:
- **Error-message string:** no other test or caller matches on the old routing-authority wording.
- **Retired starter entries:** the starter registry has none (43 entries, 0 retired, 0 disabled), so the "sync appends retired entries" idea was dropped.

No CLAUDE.md applies (none at the user level, the repo root or the changed directories), so the conventions angle found nothing.

10 findings, most severe first:

1. `puppetmaster/registry_sync.py:198`: unroutable_pin_hint looks the starter entry up by id only, so when the registry already has the same adapter and model under a different id (the 'covered' case), the hint wrongly says the entry is absent and tells the user to run `models sync --apply`.

   Failure scenario: The registry has a disabled 'cursor/my-grok' with adapter_model_name 'grok-4.5'. A user pins 'cursor/grok-4-5'. The pin fails, and the error says to run `puppetmaster models sync --apply`. Sync reports 'skip cursor/grok-4-5: cursor/my-grok is the same adapter and model' and adds nothing, so the advice loops. The real fix is to enable cursor/my-grok.

2. `puppetmaster/codegraph.py:129`: On the BaseException path (and when the 10s communicate after a timeout fails), _run_cli kills the process tree but never waits on the Popen or closes its pipes, unlike subprocess.run, which uses `with Popen` and waits.

   Failure scenario: A KeyboardInterrupt or other exception during communicate() leaves a zombie child and open stdout/stderr pipe fds until GC. If a long-lived MCP server is interrupted repeatedly, or a detached grandchild keeps the pipe open past 10s, zombies and fds pile up and ResourceWarnings appear.

3. `puppetmaster/cli/commands_models.py:676`: _run_models_sync catches only RuntimeError, but sync_starter_registry can raise OSError or PermissionError from read_text, the inter-process lock or write_private_text.

   Failure scenario: `puppetmaster models sync --apply` on a read-only ~/.puppetmaster/models.json, or one owned by another user, crashes with a Python traceback instead of `error: ...` and exit code 1.

4. `puppetmaster/registry_sync.py:174`: The apply write re-serializes the whole document with json.dumps (default ensure_ascii=True, fixed indent=2), which contradicts the docstring and docs saying existing rows stay as they are; it also skips validate_registry before writing.

   Failure scenario: A registry with notes like 'modèle rapide' or numbers like 1.50 is rewritten as 'mod\u00e8le rapide' and 1.5, and custom indentation is lost. The user sees a full-file diff after an 'append-only' sync, and nothing re-validates the merged list before it is published.

5. `puppetmaster/diagnostics.py:208`: The registry-starter-sync doctor check counts absent starter entries on adapters the platform lock disables, so a deliberately locked setup warns forever.

   Failure scenario: A user locked to cursor only, with an old registry, always gets `warn: N starter model id(s) are absent`, including every claude-code/openai entry they can never route to. The only way to clear it is to append unusable disabled rows, and that changes the registry digest and fails queued pinned tasks.

6. `puppetmaster/codegraph_repair.py:460`: The process-group fix covers only the five callers in codegraph.py; codegraph_repair still runs CodeGraph `status` through plain subprocess.run with a timeout, so the same timeout leak remains.

   Failure scenario: `codegraph status` hangs past timeout_seconds=30 (for example on a large or locked index). subprocess.run kills only the direct child, any Node children it started stay alive, and the 'no process left alive' guarantee in the changelog does not hold for repair runs.

7. `puppetmaster/registry_sync.py:171`: The apply path reads and parses the registry file twice under the lock: load_registry in _plan_for_path, then json.loads(read_text) again.

   Failure scenario: The file I/O and JSON parse are duplicated on every apply. Loading the raw document once and building the specs from it would remove the second read and any chance of the two views drifting.

8. `puppetmaster/cli/commands_models.py:742`: The CLI hard-codes the enable command string 'puppetmaster models set <id> enabled=true disabled_reason= disabled_authority=' instead of calling registry_sync.enable_command('<id>').

   Failure scenario: The same command text now lives in two places, and the CLI hint goes out of date when enable_command changes.

9. `puppetmaster/codegraph.py:112`: _run_cli sets stdout/stderr to PIPE whenever capture_output=True and silently overrides any stdout/stderr the caller passed; subprocess.run raises ValueError in that case. It also does not support `input=`, even though its docstring says it has the subprocess.run signature.

   Failure scenario: A future caller passing capture_output=True with stderr=subprocess.STDOUT, or input='...', gets separate pipes silently or a Popen TypeError instead of the documented subprocess.run behavior.

10. `tests/test_codegraph_process_group.py:51`: The timeout test gives only 3 seconds for two Python interpreter startups plus the pid-file write before the timeout fires.

    Failure scenario: On a slow or loaded CI runner (Windows, coverage enabled), the grandchild has not written child.pid within 3s, and the test fails with 'the child did not start before the timeout' even though _run_cli is correct.