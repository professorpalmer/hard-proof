import Tbl
import TblLaws

open Tbl

namespace TblGap

def base (c : Case) : Bool :=
  if (c.b5 == true) && (c.b3 == false) && (c.b4 == false) && (c.b6 == false) && (c.b0 == true) && (c.b1 == false) && (c.b8 == true) && (c.b7 == true) then false else
  if (c.b4 == true) && (c.b9 == true) && (c.b0 == true) && (c.b8 == false) && (c.b3 == true) then true else
  if (c.b9 == true) && (c.b0 == true) && (c.b8 == false) && (c.b4 == true) && (c.b3 == false) then false else
  if (c.b0 == true) && (c.b7 == false) && (c.b9 == false) && (c.b8 == false) && (c.b1 == false) && (c.b6 == false) && (c.b4 == false) then false else
  if (c.b5 == false) && (c.b7 == false) && (c.b3 == true) && (c.b4 == false) && (c.b1 == false) && (c.b8 == true) && (c.b6 == false) && (c.b0 == true) then false else
  if (c.b8 == true) && (c.b4 == false) && (c.b0 == true) && (c.b5 == false) && (c.b1 == false) && (c.b2 == false) && (c.b3 == false) && (c.b6 == true) then false else
  if (c.b6 == false) && (c.b9 == false) && (c.b4 == false) && (c.b8 == true) && (c.b7 == false) && (c.b5 == true) && (c.b1 == false) && (c.b3 == false) && (c.b2 == true) && (c.b0 == true) then false else
  if (c.b1 == false) && (c.b4 == false) && (c.b7 == true) && (c.b8 == false) && (c.b6 == true) && (c.b0 == true) then false else
  if (c.b6 == false) && (c.b1 == false) && (c.b0 == true) && (c.b3 == false) && (c.b9 == false) && (c.b4 == false) && (c.b7 == false) && (c.b2 == false) && (c.b5 == true) && (c.b8 == true) then false else
  if (c.b6 == true) && (c.b0 == true) && (c.b9 == false) && (c.b4 == true) then true else
  if (c.b5 == false) && (c.b2 == false) && (c.b7 == true) && (c.b9 == false) && (c.b0 == true) && (c.b4 == true) && (c.b8 == false) && (c.b6 == false) then false else
  if (c.b5 == true) && (c.b6 == true) && (c.b4 == false) && (c.b1 == false) && (c.b3 == false) && (c.b0 == true) && (c.b8 == true) then false else
  if (c.b1 == false) && (c.b7 == false) && (c.b8 == false) && (c.b4 == false) && (c.b0 == true) && (c.b6 == true) then true else
  if (c.b9 == false) && (c.b1 == false) && (c.b0 == true) && (c.b2 == true) && (c.b3 == false) && (c.b8 == true) && (c.b4 == false) && (c.b6 == true) && (c.b5 == false) then false else
  if (c.b4 == true) && (c.b9 == false) && (c.b6 == false) && (c.b2 == true) && (c.b8 == false) && (c.b0 == true) && (c.b5 == false) then false else
  if (c.b1 == false) && (c.b0 == true) && (c.b6 == false) && (c.b9 == true) && (c.b8 == false) && (c.b4 == false) && (c.b2 == false) then true else
  if (c.b8 == true) && (c.b1 == false) && (c.b5 == true) && (c.b3 == false) && (c.b0 == true) && (c.b9 == true) && (c.b4 == false) && (c.b6 == false) && (c.b7 == false) then true else
  if (c.b5 == false) && (c.b3 == false) && (c.b8 == true) && (c.b4 == false) && (c.b6 == false) && (c.b0 == true) && (c.b1 == false) then true else
  if (c.b4 == false) && (c.b1 == true) && (c.b0 == true) then false else
  if (c.b4 == false) && (c.b6 == false) && (c.b1 == false) && (c.b9 == true) && (c.b2 == true) && (c.b8 == false) && (c.b0 == true) then false else
  if (c.b0 == true) && (c.b5 == false) && (c.b6 == false) && (c.b2 == false) && (c.b8 == false) && (c.b7 == false) && (c.b9 == false) && (c.b4 == true) then false else
  if (c.b8 == true) && (c.b4 == true) && (c.b6 == false) && (c.b9 == false) && (c.b0 == true) then true else
  if (c.b9 == true) && (c.b8 == true) && (c.b4 == true) && (c.b0 == true) then true else
  if (c.b5 == true) && (c.b4 == false) && (c.b0 == true) && (c.b1 == false) && (c.b3 == true) && (c.b7 == false) && (c.b8 == true) then false else
  if (c.b0 == true) && (c.b8 == true) && (c.b3 == true) && (c.b7 == true) && (c.b1 == false) && (c.b4 == false) then true else
  if (c.b0 == false) && (c.b2 == true) then true else
  if (c.b4 == true) && (c.b2 == false) && (c.b0 == false) then false else
  if (c.b4 == true) && (c.b9 == false) && (c.b0 == true) && (c.b6 == false) && (c.b5 == true) && (c.b8 == false) then false else
  if (c.b1 == false) && (c.b0 == true) && (c.b8 == true) && (c.b4 == false) && (c.b9 == true) && (c.b6 == true) && (c.b2 == true) && (c.b3 == false) && (c.b5 == false) then false else
  if (c.b2 == false) && (c.b4 == false) && (c.b0 == false) then false else
  if (c.b7 == false) && (c.b6 == true) && (c.b0 == true) && (c.b1 == false) && (c.b3 == true) && (c.b8 == true) && (c.b4 == false) && (c.b5 == false) then false else
  false

def designA : Decide := base

def input : Case := ⟨true,false,false,false,false,false,false,true,false,false⟩

def designB : Decide := fun c => if c = input then true else base c

theorem a_passes : Passes designA := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
  (intro c; rcases c with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9; decide +kernel)

theorem b_passes : Passes designB := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
  (intro c; rcases c with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9; decide +kernel)

theorem differ : designA input ≠ designB input := by
  simp [designA, designB, input, base]

end TblGap
