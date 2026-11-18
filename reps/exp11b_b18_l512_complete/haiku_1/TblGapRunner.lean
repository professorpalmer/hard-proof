/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). Prints the question for the human.
-/
import Tbl
import TblGapSolution

open Tbl

def main : IO Unit := do
  let c := TblGap.input
  IO.println s!"case: b0={c.b0} b1={c.b1} b2={c.b2} b3={c.b3} b4={c.b4} b5={c.b5} b6={c.b6} b7={c.b7} b8={c.b8} b9={c.b9} b10={c.b10} b11={c.b11} b12={c.b12} b13={c.b13} b14={c.b14} b15={c.b15} b16={c.b16} b17={c.b17}"
  IO.println s!"rule A: {TblGap.designA c}"
  IO.println s!"rule B: {TblGap.designB c}"
