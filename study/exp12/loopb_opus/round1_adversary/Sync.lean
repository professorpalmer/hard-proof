/-
Hard Proof, experiment 12, second set. HUMAN-OWNED FILE.

The model of `puppetmaster models sync` (Puppetmaster v1.51.0). The command
adds the starter models that a registry lacks. The real code is
`puppetmaster.registry_sync.plan_starter_sync`.

This file has the types, the words that a law can use, and `ref`, a mirror of
the shipped code. It has no law. `DESCRIPTION.md` has the sentences of the
documentation.
-/

namespace Sync

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

/-- The registry lacks a starter entry when it has no row with that id, and no
row with that adapter and model. -/
def absent (r : List Entry) (s : Entry) : Bool :=
  !(hasId r s.id) && !(hasIdentity r s.adapter s.model)

/-- A legal starter list has no two entries with one id. An entry that is in
the list two times is not legal. -/
def DistinctIds (st : List Entry) : Prop :=
  st.Pairwise (fun a b => a.id ≠ b.id)

/-! ## The mirror of the shipped code

A law must not name `adjust` or `ref`. -/

/-- `_synced_spec` in the Python code. -/
def adjust (c : Config) (s : Entry) : Entry :=
  if !s.enabled || (c.enable && !c.locked s.adapter) then s else { s with enabled := false }

/-- `plan_starter_sync` plus the append in `sync_starter_registry`. -/
def ref : SyncImpl :=
  fun c st r => r ++ (st.filter (absent r)).map (adjust c)

end Sync
