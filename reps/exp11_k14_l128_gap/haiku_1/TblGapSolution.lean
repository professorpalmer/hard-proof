/-
Hard Proof, experiment 11. Adversary solution: a gap exists.

No law constrains the case with b2 = false, b13 = true, b11 = true, b6 = true,
b12 = true, b8 = false (the law for it is missing: there is no `Leaf71`).
`designB` is `ref` with that region flipped. Both rules pass every law.
-/
import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule: the reference rule. -/
def designA : Decide := ref

/-- The second recovery rule: the reference rule, flipped on the unconstrained region. -/
def designB : Decide := fun c =>
  if c.b2 = false ∧ c.b13 = true ∧ c.b11 = true ∧ c.b6 = true ∧ c.b12 = true ∧ c.b8 = false
  then false else ref c

/-- The case on which the two rules differ. -/
def input : Case :=
  { b0 := false, b1 := false, b2 := false, b3 := false, b4 := false, b5 := false,
    b6 := true, b7 := false, b8 := false, b9 := false, b10 := false, b11 := true,
    b12 := true, b13 := true }

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes
  repeat' apply And.intro
  all_goals (intro c; repeat intro; simp_all [designA, ref])

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes
  repeat' apply And.intro
  all_goals (intro c; repeat intro; simp_all [designB, ref])

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide

end TblGap
