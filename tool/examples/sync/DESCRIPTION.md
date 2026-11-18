# `puppetmaster models sync`, in the words of its own documentation

Ported from `exp12/base/DESCRIPTION.md`. Each quoted sentence is from
Puppetmaster v1.51.0.

From `docs/CHANGELOG.md`, section v1.51.0:

1. "`puppetmaster models sync` lists the starter ids that the registry lacks,
   for each adapter."
2. "`--apply` appends the absent entries under the registry lock, with the
   atomic writer. Each row that is in the file stays as it is: fields, key
   order, position and unknown fields."
3. "A new entry gets `enabled: false`, a `disabled_reason` that names
   `puppetmaster models sync`, and `disabled_authority: models_sync`.
   Auto-routing does not change. `--enable` keeps the starter state, but an
   entry on an adapter that the platform lock disables always gets
   `enabled: false`."
4. "A starter entry is not added when the registry has the same adapter and
   model below a different id."

From `docs/MODEL_ROUTING.md`:

5. "`models sync` adds only the entries that your registry lacks."
6. "New entries go to the end of the file."

From the docstring of `puppetmaster/registry_sync.py`:

7. "It never changes an entry that is already in the file."

## Model words and documentation words

| Model word | Documentation word |
| --- | --- |
| `Entry` | a registry row or a starter entry: id, adapter, model, `enabled` |
| `Input.enable` | the `--enable` flag |
| `Input.locked`, `isLocked` | the adapters that the platform lock disables |
| `Input.starter` | the starter registry of the release |
| `Input.registry` | the registry file |
| `Impl` | the command with `--apply`: the result is the new registry |
| `absent r s` | the registry `r` lacks the starter entry `s` |
| `added f x` | the new entries (the result without the old rows) |
| `Legal` | a starter list with no two entries with one id |

The documentation does not say in which order the new entries go to the end
of the file. `Laws.lean` has no law for that order.
