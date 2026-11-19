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
  unfold Passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hk hd
    simp [designB, hk, hd]
  · intro c hk hr
    simp [designB, hk, hr]
  · intro c hk ha hr
    simp [designB, hk, ha, hr]
  · intro c a hk ha hlt
    simp [designB, hk, ha] <;> omega
  · intro c a hk ha hlt
    simp [designB, hk, ha] <;> omega
  · intro c hk a s
    simp [designB, hk]

theorem differ : designA input ≠ designB input := by
  simp [designA, designB, ref, input]

end RecoverGap
