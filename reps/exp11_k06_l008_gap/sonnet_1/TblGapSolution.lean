import Tbl
import TblLaws

open Tbl

namespace TblGap

def designA : Decide := ref

def designB : Decide := fun c =>
  if c.b1 = false ∧ c.b0 = false ∧ c.b2 = false ∧ c.b4 = true then false else ref c

def input : Case := ⟨false, false, false, false, true, false⟩

theorem a_passes : Passes designA := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c; cases c with | mk b0 b1 b2 b3 b4 b5 => cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [designA, ref]

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro c; cases c with | mk b0 b1 b2 b3 b4 b5 => cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [designB, ref]

theorem differ : designA input ≠ designB input := by
  simp [designA, designB, input, ref]

end TblGap
