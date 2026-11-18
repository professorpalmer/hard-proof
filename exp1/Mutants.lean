/-
Hard Proof, experiment 1. HUMAN-OWNED FILE.

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

end Mutants
