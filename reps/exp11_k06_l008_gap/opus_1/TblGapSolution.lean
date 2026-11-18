import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule. -/
def designA : Decide := ref

/-- The second recovery rule: `ref`, but false on the leaf that no law covers. -/
def designB : Decide := fun c =>
  if c.b1 = false ∧ c.b0 = false ∧ c.b2 = false ∧ c.b4 = true then false else ref c

/-- The case on which the two rules differ. -/
def input : Case := ⟨false, false, false, false, true, false⟩

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c <;> rcases c with ⟨b0, b1, b2, b3, b4, b5⟩ <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c <;> rcases c with ⟨b0, b1, b2, b3, b4, b5⟩ <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide

end TblGap
