/-
Hard Proof, experiment 10. HUMAN-OWNED FILE (part of the link).

Each input line is one case: `pidKnown alive reused age staleAfter`, with 0 or 1
for the flags and `-` for an unknown age. The output line is `1` when `ref`
removes the lock file, else `0`.
-/
import Recover

open Recover

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let raw ← stdin.getLine
  if raw.isEmpty then
    return
  let line := String.ofList (raw.toList.filter (fun c => c != '\n' && c != '\r'))
  match line.splitOn " " with
  | [k, a, r, age, st] =>
    let c : Case := { pidKnown := k == "1", alive := a == "1", reused := r == "1",
                      age := age.toNat?, staleAfter := st.toNat?.getD 0 }
    stdout.putStrLn (if ref c then "1" else "0")
  | _ => throw (IO.userError s!"bad case line: {line}")
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
