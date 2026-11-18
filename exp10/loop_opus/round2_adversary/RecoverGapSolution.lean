import Recover
import RecoverLaws

open Recover

namespace RecoverGap

/-- The first recovery rule. -/
def designA : Decide := ref

/-- The second recovery rule. -/
def designB : Decide := fun c =>
  (c.pidKnown && !(c.alive && !c.reused)) ||
  (!c.pidKnown && (match c.age with
    | some a => decide (a > c.staleAfter)
    | none => false))

/-- The case on which the two rules differ. -/
def input : Case := { pidKnown := false, alive := false, reused := false,
                      age := some 0, staleAfter := 0 }

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := ref_passes

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hk ha
    simp [designB, hk, ha]
  · intro c hk hr
    simp [designB, hk, hr]
  · intro c hk ha hr
    simp [designB, hk, ha, hr]
  · intro c a hk hage hlt
    simp [designB, hk, hage]
    omega
  · intro c a hk hage hlt
    simp [designB, hk, hage]
    omega
  · intro c age s hk
    simp [designB, hk]
  · intro c hk hage
    simp [designB, hk, hage]

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  simp [designA, designB, ref, input]

end RecoverGap
