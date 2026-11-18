/-
Hard Proof, experiment 8. HUMAN-OWNED FILE (part of the link).

The model runner. Each input line is one case:
    <enable 0|1>|<locked adapters, comma>|<starter rows>|<registry rows>
A row is `id,adapter,model,enabled`, and rows are joined with `;`.
The output line is the rows of `refSync` for that case.
-/
import SyncLaws

open SyncLaws

def parseNats (s : String) : List Nat :=
  if s.isEmpty then [] else (s.splitOn ",").filterMap String.toNat?

def parseRows (s : String) : List Entry :=
  if s.isEmpty then [] else
    (s.splitOn ";").filterMap fun row =>
      match (row.splitOn ",").filterMap String.toNat? with
      | [i, a, m, e] => some ⟨i, a, m, e != 0⟩
      | _ => none

def showRows (rows : List Entry) : String :=
  ";".intercalate (rows.map fun e => s!"{e.id},{e.adapter},{e.model},{if e.enabled then 1 else 0}")

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let raw ← stdin.getLine
  if raw.isEmpty then
    return
  let line := String.ofList (raw.toList.filter (fun c => c != '\n' && c != '\r'))
  match line.splitOn "|" with
  | [en, locked, st, reg] =>
    let lockedList := parseNats locked
    let c : Config := { locked := fun a => lockedList.contains a, enable := en == "1" }
    stdout.putStrLn (showRows (refSync c (parseRows st) (parseRows reg)))
  | _ => throw (IO.userError s!"bad case line: {line}")
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
