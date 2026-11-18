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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hk ha
    simp [designB, ref, hk, ha]
  · intro c hk hr
    simp [designB, ref, hk, hr]
  · intro c hk ha hr
    simp [designB, ref, hk, ha, hr]
  · intro c a hk hage hlt
    simp [designB, ref, hk, hage]
    omega
  · intro c a hk hage hlt
    simp [designB, ref, hk, hage]
    omega
  · intro c age s hk
    simp [designB, ref, hk]

theorem differ : designA input ≠ designB input := by
  decide

end RecoverGap
