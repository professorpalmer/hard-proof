/-
Hard Proof, experiment 3. HUMAN-OWNED FILE.

The challenge. Each `sorry` is a hole that the agent must fill in `Solution.lean`.
`lake comparator` accepts the solution only when each theorem there has the same
statement as the theorem here.

`Exp.lock` is a definition hole: it is the code under test.
-/
import Laws
import Mutants

open Laws

namespace Exp

/-- The lock design. The agent supplies it. -/
def lock : LockImpl := sorry

/-- Law 1 holds for the lock. -/
theorem mutex : Mutex lock := sorry

/-- Law 2 holds for the lock. -/
theorem no_orphan_hold : NoOrphanHold lock := sorry

/-- Law 2 is not vacuous for the lock: the lock can refuse. -/
theorem can_refuse : CanRefuse lock := sorry

/-- Law 1 is not vacuous for the lock: a process can enter. -/
theorem can_enter : CanEnter lock := sorry

/-- Mutant kill: Law 2 is false for the pid-only lock. -/
theorem kill_pid_only : ¬ NoOrphanHold Mutants.pidOnly := sorry

/-- Recorded fact from experiment 1: Law 1 is true for the pid-only lock.
Law 1 alone cannot catch the pid-reuse bug. -/
theorem mutex_alone_misses_pid_only : Mutex Mutants.pidOnly := sorry

/-- Law 3 holds for the lock. -/
theorem holder_keeps_lock : HolderKeepsLock lock := sorry

/-- Mutant kill: Law 3 is false for the lock that always grants. -/
theorem kill_always_grant : ¬ HolderKeepsLock Mutants.alwaysGrant := sorry

end Exp
