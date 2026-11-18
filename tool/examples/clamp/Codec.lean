/-
hardproof domain `clamp`. AUTHOR FILE (pinned).

An input line is `x,lo,hi` in decimal. An output line is the decimal result.
-/
import Types

namespace HP

def decodeInput (s : String) : Option Input :=
  match (s.splitOn ",").map String.toInt? with
  | [some x, some lo, some hi] => some ⟨x, lo, hi⟩
  | _ => none

def encodeInput (i : Input) : String := s!"{i.x},{i.lo},{i.hi}"

def encodeOutput (o : Output) : String := toString o

def showInput (i : Input) : String := s!"clamp(x={i.x}, lo={i.lo}, hi={i.hi})"

def showOutput (o : Output) : String := toString o

end HP
