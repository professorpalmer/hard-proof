/-
Hard Proof, experiment 10. HUMAN-OWNED FILE.

Third domain: the stale-lock recovery rule of the real lock
(`puppetmaster.interprocess_lock.InterProcessFileLock._recover_stale_owner`).

This file has the model types and `ref`, a mirror of the shipped Python code.
It has no laws. In this experiment an agent writes the laws from the English
description of the rule.
-/

namespace Recover

/-- What the recovery step knows when it finds a lock file. -/
structure Case where
  /-- The lock record has a valid owner pid. -/
  pidKnown : Bool
  /-- The kernel says that a process with the owner pid exists. -/
  alive : Bool
  /-- The owner pid now names a later process than the recorded owner. -/
  reused : Bool
  /-- The age of the lock in seconds, when the age is known. -/
  age : Option Nat
  /-- The `stale_after` setting in seconds. -/
  staleAfter : Nat
deriving DecidableEq, Repr

/-- A recovery rule. `true` means: remove the lock file. -/
abbrev Decide := Case → Bool

/-- The mirror of the shipped code. -/
def ref : Decide := fun c =>
  (c.pidKnown && !(c.alive && !c.reused)) ||
  (!c.pidKnown && (match c.age with
    | some a => decide (a ≥ c.staleAfter)
    | none => false))

end Recover
