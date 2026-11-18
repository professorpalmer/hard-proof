/-
Hard Proof, experiment 6. HUMAN-OWNED FILE.

Prints the question for the human: the state of the two designs after each
event of the trace. Run it only after the gap gate accepts.
-/
import Laws
import GapSolution

open Laws

def showProc (p : Proc) : String := s!"{p.pid}:{p.tok}"

def showEvent : Event → String
  | .spawn n => s!"spawn {n}"
  | .exit n => s!"exit {n}"
  | .acquire n => s!"acquire {n}"
  | .release n => s!"release {n}"

def inside {I : LockImpl} (s : State I) (procs : List Proc) : String :=
  let xs := procs.filter (fun p => s.cs p)
  if xs.isEmpty then "none" else ",".intercalate (xs.map showProc)

def main : IO Unit := do
  let mut a := init Gap.designA
  let mut b := init Gap.designB
  let mut procs : List Proc := []
  IO.println s!"who={showProc Gap.who}"
  for e in Gap.trace do
    let before := a.os.table
    a := step Gap.designA a e
    b := step Gap.designB b e
    match e with
    | .spawn pid =>
      match before pid, a.os.table pid with
      | none, some t => procs := procs ++ [⟨pid, t⟩]
      | _, _ => pure ()
    | _ => pure ()
    IO.println s!"event={showEvent e} A_inside={inside a procs} B_inside={inside b procs} A_grants={grants Gap.designA a} B_grants={grants Gap.designB b}"
