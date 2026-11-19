import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule. -/
def designA : Decide := ref

/-- The second recovery rule: it differs from `ref` only in the region of the missing law (Leaf71). -/
def designB : Decide := fun c =>
  if (!c.b2 && c.b13 && c.b11 && c.b6 && c.b12 && !c.b8) = true then false else ref c

/-- The case on which the two rules differ. -/
def input : Case :=
  { b0 := false, b1 := false, b2 := false, b3 := false, b4 := false, b5 := false, b6 := true,
    b7 := false, b8 := false, b9 := false, b10 := false, b11 := true, b12 := true, b13 := true }

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes
  repeat' constructor
  all_goals
    intro ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩
    dsimp only
    intros
    subst_vars
    rfl

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes
  repeat' constructor
  all_goals
    intro ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩
    dsimp only
    intros
    subst_vars
    rfl

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by decide

end TblGap
