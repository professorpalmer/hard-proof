/-
Gap witness. The law set has no law for the rule leaf with the path
b4 = true, b1 = false, b14 = false, b3 = true, b8 = true, b16 = true,
b6 = false, b10 = false, b12 = false, b15 = true (law Leaf349 is absent).
Two rules that differ only on that path both pass every law.
-/
import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule: the reference rule. -/
def designA : Decide := ref

/-- The second recovery rule: the reference rule, with the answer flipped on the path with no law. -/
def designB : Decide := fun c =>
  if (c.b4 && !c.b1 && !c.b14 && c.b3 && c.b8 && c.b16 && !c.b6 && !c.b10 && !c.b12 && c.b15) = true
  then !ref c else ref c

/-- The case on which the two rules differ. -/
def input : Case :=
  { b0 := false, b1 := false, b2 := false, b3 := true, b4 := true, b5 := false,
    b6 := false, b7 := false, b8 := true, b9 := false, b10 := false, b11 := false,
    b12 := false, b13 := false, b14 := false, b15 := true, b16 := true, b17 := false }

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  repeat' apply And.intro
  all_goals (intro c; intros; simp_all [designA, ref])

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  repeat' apply And.intro
  all_goals (intro c; intros; simp_all [designB, ref])

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide

end TblGap
