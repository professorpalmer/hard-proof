/-
Hard Proof, experiment 11. Adversary solution: a gap exists.

No law constrains the case b1 = false, b0 = false, b2 = false, b4 = true.
`designA` is the reference rule and answers true there. `designB` answers false
there and agrees with the reference rule everywhere else. Both pass every law.
-/
import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule. -/
def designA : Decide := Tbl.ref

/-- The second recovery rule. -/
def designB : Decide := fun c =>
  if c.b1 = false && c.b0 = false && c.b2 = false && c.b4 = true then false else Tbl.ref c

/-- The case on which the two rules differ. -/
def input : Case := ⟨false, false, false, false, true, false⟩

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes Leaf0 Leaf2 Leaf3 Leaf4 Leaf5 Leaf6 Leaf7 designA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c
    rcases c with ⟨b0, b1, b2, b3, b4, b5⟩
    intros
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
      simp_all [Tbl.ref]

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes Leaf0 Leaf2 Leaf3 Leaf4 Leaf5 Leaf6 Leaf7 designB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c
    rcases c with ⟨b0, b1, b2, b3, b4, b5⟩
    intros
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
      simp_all [Tbl.ref]

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide

end TblGap
