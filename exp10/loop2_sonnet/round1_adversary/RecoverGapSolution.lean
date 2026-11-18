import Recover
import RecoverLaws

open Recover

namespace RecoverGap

def designA : Decide := ref

def designB : Decide := fun c =>
  if c.pidKnown = false ∧ c.age = none then true else ref c

def input : Case := ⟨false, false, false, none, 0⟩

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hp ha; simp [designB, ref, hp, ha]
  · intro c hp hr; simp [designB, ref, hp, hr]
  · intro c hp ha hr; simp [designB, ref, hp, ha, hr]
  · intro c hp a hage hge; simp [designB, ref, hp, hage]; omega
  · intro c d hc hd ha hr; simp [designB, ref, hc, hd, ha, hr]
  · intro c hp a hage hlt; simp [designB, ref, hp, hage]; omega

theorem differ : designA input ≠ designB input := by
  simp [designA, designB, input, ref]

end RecoverGap
