/-
Hard Proof, experiment 6. HUMAN-OWNED FILE.

The gap challenge. It asks an adversary to show that the laws leave behavior
open: two lock designs pass each law, and one sequence of events puts a process
in the critical section for one design and not for the other design.

Each `sorry` is a hole. The adversary fills the holes in `GapSolution.lean`.
`lake comparator` accepts only when each statement there is the same as here.
-/
import Laws

open Laws

namespace Gap

/-- The first design. -/
def designA : LockImpl := sorry

/-- The second design. -/
def designB : LockImpl := sorry

/-- The sequence of events on which the two designs differ. -/
def trace : List Event := sorry

/-- The process that is inside for one design and outside for the other. -/
def who : Proc := sorry

/-- The first design passes each law. -/
theorem a_passes : Passes designA := sorry

/-- The second design passes each law. -/
theorem b_passes : Passes designB := sorry

/-- After `trace`, `who` is in the critical section for one design only. -/
theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := sorry

end Gap
