/-
Hard Proof, experiment 10. HUMAN-OWNED FILE.

The gap challenge for an agent-written law set (`RecoverLaws.lean`).
Each `sorry` is a hole. The adversary fills the holes in `RecoverGapSolution.lean`.
-/
import Recover
import RecoverLaws

open Recover

namespace RecoverGap

/-- The first recovery rule. -/
def designA : Decide := sorry

/-- The second recovery rule. -/
def designB : Decide := sorry

/-- The case on which the two rules differ. -/
def input : Case := sorry

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := sorry

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := sorry

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := sorry

end RecoverGap
