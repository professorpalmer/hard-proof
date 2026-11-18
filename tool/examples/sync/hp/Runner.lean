-- hardproof: TOOL-OWNED FILE. The tool writes it again before each check.
-- Reads one encoded input on each line of stdin. Prints `encodeOutput (ref x)`
-- for each line, or `DECODE_ERROR` when the line does not decode.
import Types
import Ref
import Codec

open HP

partial def hpLoop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let raw ← stdin.getLine
  if raw.isEmpty then
    return
  let line := String.ofList (raw.toList.filter (fun c => c != '\n' && c != '\r'))
  match decodeInput line with
  | some x => stdout.putStrLn (encodeOutput (ref x))
  | none => stdout.putStrLn "DECODE_ERROR"
  hpLoop stdin stdout

def main : IO Unit := do
  hpLoop (← IO.getStdin) (← IO.getStdout)
