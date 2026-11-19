/-
Hard Proof, experiment 8. HUMAN-OWNED FILE.

Second domain: `puppetmaster models sync` (Puppetmaster v1.51.0). The command
adds the starter models that a registry lacks. The real code is
`puppetmaster.registry_sync.plan_starter_sync`.

This file holds the model, the laws, and `refSync`. The laws are the sentences
of the v1.51.0 changelog, one law for each sentence. `refSync` is a model of
the shipped Python code, line for line. A link test compares `refSync` with
the real code.
-/

namespace SyncLaws

/-- One registry row. `adapter` and `model` together are the execution identity. -/
structure Entry where
  id : Nat
  adapter : Nat
  model : Nat
  enabled : Bool
deriving DecidableEq, Repr

/-- The settings of one sync run. -/
structure Config where
  /-- The platform lock disables this adapter. -/
  locked : Nat → Bool
  /-- The `--enable` flag. -/
  enable : Bool

/-- A sync design: settings, starter list, registry. The result is the new registry. -/
abbrev SyncImpl := Config → List Entry → List Entry → List Entry

def hasId (r : List Entry) (i : Nat) : Bool := r.any (fun e => e.id == i)

def hasIdentity (r : List Entry) (a m : Nat) : Bool :=
  r.any (fun e => e.adapter == a && e.model == m)

/-- A starter entry is absent when the registry has no row with its id, and no
row with its adapter and model. -/
def absent (r : List Entry) (s : Entry) : Bool :=
  !(hasId r s.id) && !(hasIdentity r s.adapter s.model)

/-- The starter list has no two entries with one id. -/
def DistinctIds (st : List Entry) : Prop :=
  ∀ s ∈ st, ∀ s' ∈ st, s.id = s'.id → s = s'

/-! ## The model of the shipped code -/

/-- `_synced_spec` in the Python code. -/
def adjust (c : Config) (s : Entry) : Entry :=
  if !s.enabled || (c.enable && !c.locked s.adapter) then s else { s with enabled := false }

/-- `plan_starter_sync` plus the append in `sync_starter_registry`. -/
def refSync : SyncImpl :=
  fun c st r => r ++ (st.filter (absent r)).map (adjust c)

/-! ## Laws: one for each sentence of the changelog -/

/-- Law 1. "Each row that is in the file stays as it is: fields, key order, position." -/
def KeepsRows (f : SyncImpl) : Prop :=
  ∀ c st r, ∃ added, f c st r = r ++ added

/-- Law 2. The command adds starter entries that the registry lacks, and no other row. -/
def OnlyAbsentStarter (f : SyncImpl) : Prop :=
  ∀ c st r added, f c st r = r ++ added →
    ∀ a ∈ added, ∃ s ∈ st, absent r s = true ∧ a.id = s.id ∧ a.adapter = s.adapter ∧ a.model = s.model

/-- Law 3. After the command, the registry has each starter id that was absent. -/
def NothingLeft (f : SyncImpl) : Prop :=
  ∀ c st r, ∀ s ∈ st, absent r s = true → hasId (f c st r) s.id = true

/-- Law 4. "A new entry gets `enabled: false`." (without `--enable`) -/
def DisabledByDefault (f : SyncImpl) : Prop :=
  ∀ c st r added, c.enable = false → f c st r = r ++ added → ∀ a ∈ added, a.enabled = false

/-- Law 5. "An entry on an adapter that the platform lock disables always gets `enabled: false`." -/
def LockedStaysDisabled (f : SyncImpl) : Prop :=
  ∀ c st r added, f c st r = r ++ added → ∀ a ∈ added, c.locked a.adapter = true → a.enabled = false

/-- Law 6. "`--enable` keeps the starter state." -/
def EnableKeepsStarterState (f : SyncImpl) : Prop :=
  ∀ c st r added, DistinctIds st → c.enable = true → f c st r = r ++ added →
    ∀ a ∈ added, c.locked a.adapter = false → ∃ s ∈ st, s.id = a.id ∧ a.enabled = s.enabled

/-- Law 7. A second run changes nothing. -/
def Idempotent (f : SyncImpl) : Prop :=
  ∀ c st r, f c st (f c st r) = f c st r

/-- The key of a row: id, adapter, model. -/
def key (e : Entry) : Nat × Nat × Nat := (e.id, e.adapter, e.model)

/-- Law 8. The new rows are the absent starter entries, one time each, in
starter order. Added after experiment 8c: adversaries showed that laws 1 to 7
allow a different row order, and allow each new row two times. -/
def ExactAdditions (f : SyncImpl) : Prop :=
  ∀ c st r added, f c st r = r ++ added → added.map key = (st.filter (absent r)).map key

/-- A design passes when each law holds for it. -/
def Passes (f : SyncImpl) : Prop :=
  KeepsRows f ∧ OnlyAbsentStarter f ∧ NothingLeft f ∧ DisabledByDefault f ∧
  LockedStaysDisabled f ∧ EnableKeepsStarterState f ∧ Idempotent f ∧ ExactAdditions f

/-! ## Pinned examples

One registry row, four starter entries. Entry 1 is in the registry by id.
Entry 3 has a new id but the adapter and model of entry 1. Adapter 2 is locked. -/

private def reg : List Entry := [⟨1, 1, 1, true⟩]
private def starter : List Entry :=
  [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩, ⟨3, 1, 1, true⟩, ⟨4, 2, 5, true⟩]
private def lock2 (enable : Bool) : Config := { locked := fun a => a == 2, enable := enable }

example : absent reg ⟨2, 1, 2, true⟩ = true := by decide
example : absent reg ⟨1, 1, 1, true⟩ = false := by decide
example : absent reg ⟨3, 1, 1, true⟩ = false := by decide
-- Without `--enable`, each new entry is disabled.
example : refSync (lock2 false) starter reg = reg ++ [⟨2, 1, 2, false⟩, ⟨4, 2, 5, false⟩] := by decide
-- With `--enable`, the entry on the locked adapter stays disabled.
example : refSync (lock2 true) starter reg = reg ++ [⟨2, 1, 2, true⟩, ⟨4, 2, 5, false⟩] := by decide
-- A second run changes nothing.
example : refSync (lock2 false) starter (refSync (lock2 false) starter reg)
    = refSync (lock2 false) starter reg := by decide

end SyncLaws
