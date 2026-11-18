import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule: true exactly where a law with answer true applies. -/
def designA : Decide := fun c =>
  (c.b4 && c.b9 && c.b0 && !c.b8 && c.b3) ||
  (c.b6 && c.b0 && !c.b9 && c.b4) ||
  (!c.b1 && !c.b7 && !c.b8 && !c.b4 && c.b0 && c.b6) ||
  (!c.b1 && c.b0 && !c.b6 && c.b9 && !c.b8 && !c.b4 && !c.b2) ||
  (c.b8 && !c.b1 && c.b5 && !c.b3 && c.b0 && c.b9 && !c.b4 && !c.b6 && !c.b7) ||
  (!c.b5 && !c.b3 && c.b8 && !c.b4 && !c.b6 && c.b0 && !c.b1) ||
  (c.b8 && c.b4 && !c.b6 && !c.b9 && c.b0) ||
  (c.b9 && c.b8 && c.b4 && c.b0) ||
  (c.b0 && c.b8 && c.b3 && c.b7 && !c.b1 && !c.b4) ||
  (!c.b0 && c.b2)

/-- The case on which the two rules differ. No law applies to it. -/
def input : Case :=
  { b0 := true, b1 := false, b2 := false, b3 := false, b4 := false,
    b5 := false, b6 := false, b7 := true, b8 := false, b9 := false }

/-- The second recovery rule: the same as `designA`, except on `input`. -/
def designB : Decide := fun c => designA c || decide (c = input)

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro c; cases c with | mk b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9; decide)

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro c; cases c with | mk b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9; decide)

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by decide

end TblGap
