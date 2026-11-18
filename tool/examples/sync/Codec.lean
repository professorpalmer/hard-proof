/-
hardproof domain `sync`. AUTHOR FILE (pinned).

An input line is `<enable 0|1>|<locked adapters, comma>|<starter rows>|<registry rows>`.
A row is `id,adapter,model,enabled` and rows are joined with `;`. An output
line is the rows of the new registry in the same row format.
-/
import Types

namespace HP

def decodeNats (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM String.toNat?

def decodeRow (s : String) : Option Entry :=
  match (s.splitOn ",").mapM String.toNat? with
  | some [i, a, m, 0] => some ⟨i, a, m, false⟩
  | some [i, a, m, 1] => some ⟨i, a, m, true⟩
  | _ => none

def decodeRows (s : String) : Option (List Entry) :=
  if s.isEmpty then some [] else (s.splitOn ";").mapM decodeRow

def encodeRows (rows : List Entry) : String :=
  ";".intercalate (rows.map fun e => s!"{e.id},{e.adapter},{e.model},{if e.enabled then 1 else 0}")

def decodeInput (s : String) : Option Input :=
  match s.splitOn "|" with
  | [en, locked, st, reg] => do
    let e ← (if en == "1" then some true else if en == "0" then some false else none)
    let l ← decodeNats locked
    let st ← decodeRows st
    let reg ← decodeRows reg
    pure ⟨e, l, st, reg⟩
  | _ => none

def encodeInput (x : Input) : String :=
  s!"{if x.enable then 1 else 0}|{",".intercalate (x.locked.map toString)}|{encodeRows x.starter}|{encodeRows x.registry}"

def encodeOutput (o : Output) : String := encodeRows o

def showRows (rows : List Entry) : String :=
  "[" ++ "; ".intercalate (rows.map fun e =>
    s!"id {e.id} (adapter {e.adapter}, model {e.model}, {if e.enabled then "enabled" else "disabled"})") ++ "]"

def showInput (x : Input) : String :=
  s!"enable_flag={x.enable} locked_adapters={x.locked} starter={showRows x.starter} registry={showRows x.registry}"

def showOutput (o : Output) : String := showRows o

end HP
