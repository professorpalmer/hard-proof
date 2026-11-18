# `puppetmaster models sync`, in the words of its own documentation

Each quoted sentence is from Puppetmaster v1.51.0.

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

## How the model maps to these words

- A registry and a starter list are each a `List Entry`. An `Entry` has an id,
  an adapter, a model, and an `enabled` flag. The model has no other field.
- `Config.enable` is the `--enable` flag. `Config.locked a` is true when the
  platform lock disables adapter `a`.
- A `SyncImpl` is the command with `--apply`: it takes the settings, the
  starter list and the registry, and returns the new registry.
- `absent r s` is true when registry `r` lacks starter entry `s`.
- A legal starter list has no two entries with one id (`DistinctIds`).
