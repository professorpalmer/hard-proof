import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule. -/
def designA : Decide := fun c =>
  if c.b2 = true ∧ c.b6 = false ∧ c.b8 = false ∧ c.b9 = true ∧ c.b4 = true ∧ c.b7 = false ∧ c.b0 = false
  then true else ref c

/-- The second recovery rule. -/
def designB : Decide := fun c =>
  if c.b2 = true ∧ c.b6 = false ∧ c.b8 = false ∧ c.b9 = true ∧ c.b4 = true ∧ c.b7 = false ∧ c.b0 = false
  then false else ref c

/-- The case on which the two rules differ. -/
def input : Case :=
  { b0 := false, b1 := false, b2 := true, b3 := false, b4 := true,
    b5 := false, b6 := false, b7 := false, b8 := false, b9 := true }

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes Leaf0 Leaf1 Leaf2 Leaf3 Leaf4 Leaf5 Leaf6 Leaf7 Leaf8 Leaf9 Leaf10 Leaf11
    Leaf12 Leaf13 Leaf14 Leaf15 Leaf16 Leaf17 Leaf18 Leaf19 Leaf20 Leaf21 Leaf22 Leaf23
    Leaf24 Leaf26 Leaf27 Leaf28 Leaf29 Leaf30 Leaf31
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c; intros; simp_all [designA, ref]

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes Leaf0 Leaf1 Leaf2 Leaf3 Leaf4 Leaf5 Leaf6 Leaf7 Leaf8 Leaf9 Leaf10 Leaf11
    Leaf12 Leaf13 Leaf14 Leaf15 Leaf16 Leaf17 Leaf18 Leaf19 Leaf20 Leaf21 Leaf22 Leaf23
    Leaf24 Leaf26 Leaf27 Leaf28 Leaf29 Leaf30 Leaf31
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c; intros; simp_all [designB, ref]

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide

end TblGap
