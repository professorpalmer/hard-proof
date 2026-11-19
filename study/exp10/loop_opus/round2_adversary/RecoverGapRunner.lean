/-
Hard Proof, experiment 10. HUMAN-OWNED FILE.

Prints the question for the human: the case, the answer of each of the two
rules, and the answer of the shipped code (`ref`).
-/
import Recover
import RecoverGapSolution

open Recover

def yesNo (b : Bool) : String := if b then "remove the lock file" else "keep the lock file"

def main : IO Unit := do
  let c := RecoverGap.input
  let age := match c.age with
    | some a => s!"{a} s"
    | none => "unknown"
  IO.println s!"case: owner pid known={c.pidKnown} pid alive={c.alive} pid reused={c.reused} age={age} stale_after={c.staleAfter} s"
  IO.println s!"rule A: {yesNo (RecoverGap.designA c)}"
  IO.println s!"rule B: {yesNo (RecoverGap.designB c)}"
  IO.println s!"shipped code: {yesNo (ref c)}"
