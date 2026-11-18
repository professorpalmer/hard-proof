import Tbl
import TblLaws

open Tbl

namespace TblGap

def designA : Decide := fun c =>
  if c.b0 = true ∧ c.b2 = false then (c.b4 && !c.b5 && c.b3) else true

def designB : Decide := fun c =>
  if c.b0 = true ∧ c.b2 = false then false else true

def input : Case := ⟨true, false, false, true, true, false⟩

theorem a_passes : Passes designA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c
    obtain ⟨b0, b1, b2, b3, b4, b5⟩ := c
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [designA]

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c
    obtain ⟨b0, b1, b2, b3, b4, b5⟩ := c
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [designB]

theorem differ : designA input ≠ designB input := by
  simp [designA, designB, input]

end TblGap
