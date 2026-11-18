import Tbl
import TblLaws

open Tbl

namespace TblGap

def designA : Decide := Tbl.ref

def designB : Decide := fun c =>
  if (c.b2 && !c.b6 && !c.b8 && c.b9 && c.b4 && !c.b7 && !c.b0) = true then false else Tbl.ref c

def input : Case := ⟨false, false, true, false, true, false, false, false, false, true⟩

theorem a_passes : Passes designA := by
  unfold Passes designA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (intro c; simp only [Tbl.ref]; intros; simp_all)

theorem b_passes : Passes designB := by
  unfold Passes designB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (intro c; simp only [Tbl.ref]; intros; simp_all)

theorem differ : designA input ≠ designB input := by
  decide

end TblGap
