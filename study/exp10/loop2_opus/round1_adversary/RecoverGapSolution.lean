import Recover
import RecoverLaws

open Recover

namespace RecoverGap

def designA : Decide := ref

def designB : Decide := fun c => ref c || (!c.pidKnown && c.age.isNone)

def input : Case :=
  { pidKnown := false, alive := false, reused := false, age := none, staleAfter := 0 }

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ref_passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hk ha
    simp [designB, h1 c hk ha]
  · intro c hk hr
    simp [designB, h2 c hk hr]
  · intro c hk ha hr
    simp [designB, h3 c hk ha hr, hk]
  · intro c a hk hage hlt
    simp [designB, h4 c a hk hage hlt]
  · intro c a hk hage hlt
    simp [designB, h5 c a hk hage hlt, hk, hage]
  · intro c age s hk
    simp [designB, hk]
    have := h6 c age s hk
    simp [ref, hk]

theorem differ : designA input ≠ designB input := by
  simp [designA, designB, ref, input]

end RecoverGap
