/-
Hard Proof, experiment 11. HUMAN-OWNED FILE.

The gap challenge for the generated law set (`TblLaws.lean`).
Each `sorry` is a hole. The adversary fills the holes in `TblGapSolution.lean`.
-/
import Tbl
import TblLaws

open Tbl

namespace TblGap

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

end TblGap
