/-
Hard Proof, experiment 2. HUMAN-OWNED FILE (part of the link).

The model runner. It reads events from stdin and prints the model state after
each event. It runs the same `Laws.step` and the same `Exp.lock` that experiment 1
proved.

Input lines:  spawn N | exit N | acquire N | release N | reset
Output lines: one line for each event:  owner=<pid>:<tok>|none cs=<pid>:<tok>,...|none
-/
import Laws
import Solution

open Laws

structure Sim where
  s : State Exp.lock
  /-- Each process that the OS started, in start order. -/
  procs : Array Proc

def Sim.start : Sim := { s := init Exp.lock, procs := #[] }

def Sim.next (m : Sim) (e : Event) : Sim :=
  let s' := step Exp.lock m.s e
  let procs :=
    match e with
    | .spawn pid =>
      match m.s.os.table pid, s'.os.table pid with
      | none, some t => m.procs.push ⟨pid, t⟩
      | _, _ => m.procs
    | _ => m.procs
  { s := s', procs := procs }

def showProc (p : Proc) : String := s!"{p.pid}:{p.tok}"

def Sim.render (m : Sim) : String :=
  let owner : Option Proc := m.s.owner
  let ownerText := match owner with
    | none => "none"
    | some p => showProc p
  let inside := m.procs.toList.filter (fun p => m.s.cs p)
  let csText := if inside.isEmpty then "none" else ",".intercalate (inside.map showProc)
  s!"owner={ownerText} cs={csText}"

def parseEvent (line : String) : Option Event :=
  match line.splitOn " " with
  | ["spawn", n] => n.toNat?.map Event.spawn
  | ["exit", n] => n.toNat?.map Event.exit
  | ["acquire", n] => n.toNat?.map Event.acquire
  | ["release", n] => n.toNat?.map Event.release
  | _ => none

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (m : Sim) : IO Unit := do
  let raw ← stdin.getLine
  if raw.isEmpty then
    return
  let line := String.ofList (raw.toList.filter (fun c => c != '\n' && c != '\r'))
  if line == "reset" then
    stdout.putStrLn "reset"
    loop stdin stdout Sim.start
  else
    match parseEvent line with
    | none => throw (IO.userError s!"bad event line: {line}")
    | some e =>
      let m' := m.next e
      stdout.putStrLn m'.render
      loop stdin stdout m'

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  loop stdin stdout Sim.start
