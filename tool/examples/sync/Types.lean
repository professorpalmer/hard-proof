/-
hardproof domain `sync`. AUTHOR FILE (pinned).

The model of `puppetmaster models sync` (Puppetmaster v1.51.0), ported from
experiment 12. The command adds the starter models that a registry lacks.
The real code is `puppetmaster.registry_sync.plan_starter_sync`, plus the
append in `sync_starter_registry`.

This file has the types and the words that a law can use. It has no law
and no `ref`. `DESCRIPTION.md` has the sentences of the documentation.
-/

namespace HP

/-- One registry row. `adapter` and `model` together are the execution identity. -/
structure Entry where
  id : Nat
  adapter : Nat
  model : Nat
  enabled : Bool
deriving DecidableEq, Repr

/-- One sync run: the settings, the starter list and the registry. -/
structure Input where
  /-- The `--enable` flag. -/
  enable : Bool
  /-- The adapters that the platform lock disables. -/
  locked : List Nat
  /-- The starter list of this release. -/
  starter : List Entry
  /-- The registry file. -/
  registry : List Entry
deriving DecidableEq, Repr

/-- The new registry. -/
abbrev Output := List Entry

/-- A sync design, with `--apply`. -/
abbrev Impl := Input → Output

/-- The platform lock disables adapter `a`. -/
def isLocked (x : Input) (a : Nat) : Bool := x.locked.contains a

def hasId (r : List Entry) (i : Nat) : Bool := r.any (fun e => e.id == i)

def hasIdentity (r : List Entry) (a m : Nat) : Bool :=
  r.any (fun e => e.adapter == a && e.model == m)

/-- The registry lacks a starter entry when it has no row with that id, and no
row with that adapter and model. -/
def absent (r : List Entry) (s : Entry) : Bool :=
  !(hasId r s.id) && !(hasIdentity r s.adapter s.model)

/-- The rows that a run adds: the result without the old registry rows. -/
def added (f : Impl) (x : Input) : List Entry :=
  (f x).drop x.registry.length

/-- A legal input has a starter list with pairwise distinct ids. -/
def legal (x : Input) : Bool := decide (x.starter.map Entry.id).Nodup

def Legal (x : Input) : Prop := legal x = true

end HP
