import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule. -/
def designA : Decide := fun c => !c.b0 || c.b2

/-- The second recovery rule. -/
def designB : Decide := fun c => !c.b0 || c.b2 || (c.b4 && c.b3 && !c.b5)

/-- The case on which the two rules differ. -/
def input : Case := { b0 := true, b1 := false, b2 := false, b3 := true, b4 := true, b5 := false }

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes Law0 Law1 Law2 Law3 Law4 Law5 Law6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c <;> rcases c with ⟨b0, b1, b2, b3, b4, b5⟩ <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes Law0 Law1 Law2 Law3 Law4 Law5 Law6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c <;> rcases c with ⟨b0, b1, b2, b3, b4, b5⟩ <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide

end TblGap
