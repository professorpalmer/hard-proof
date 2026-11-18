/-
Hard Proof, experiment 7. HUMAN-OWNED FILE.

Known-bad lock designs. A law set must reject each mutant: for each mutant, the
agent must prove that a minimum of one law is false.
-/
import Laws

namespace Mutants
open Laws

/-- The lock stores the pid alone. It decides "alive" when a process has that
pid. This is the pid-reuse bug class. -/
def pidOnly : LockImpl where
  Rec := Nat
  record p := p.pid
  alive os r := (os.table r).isSome
  isOwner r p := r == p.pid

/-- The lock always decides that the owner is dead. It gives the lock to each
request, also when a live process has it. -/
def alwaysGrant : LockImpl where
  Rec := Proc
  record p := p
  alive _ _ := false
  isOwner r p := decide (r = p)

end Mutants
