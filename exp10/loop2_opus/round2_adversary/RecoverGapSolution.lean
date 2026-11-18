import Recover
import RecoverLaws

open Recover

namespace RecoverGap

def designA : Decide := ref

def designB : Decide := fun c =>
  (c.pidKnown && !(c.alive && !c.reused)) ||
  (!c.pidKnown && (match c.age with
    | some a => decide (a > c.staleAfter)
    | none => false))

def input : Case :=
  { pidKnown := false, alive := false, reused := false, age := some 5, staleAfter := 5 }

theorem a_passes : Passes designA := ref_passes

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

theorem differ : designA input ≠ designB input := by
  decide

end RecoverGap
