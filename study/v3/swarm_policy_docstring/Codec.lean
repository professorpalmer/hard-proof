/-
hardproof domain `swarm_policy`. AUTHOR FILE (pinned).

An input line is four digits `0` or `1`: refusal, launch, narrow, broad.
An output line is `solo`, `explicit` or `broad`.
-/
import Types

namespace HP

def bit (c : Char) : Option Bool :=
  if c = '1' then some true else if c = '0' then some false else none

def decodeInput (s : String) : Option Input :=
  match s.toList.map bit with
  | [some r, some l, some n, some b] => some ⟨r, l, n, b⟩
  | _ => none

def digit (b : Bool) : String := if b then "1" else "0"

def encodeInput (i : Input) : String :=
  digit i.refusal ++ digit i.launch ++ digit i.narrow ++ digit i.broad

def encodeOutput : Output → String
  | Output.solo => "solo"
  | Output.explicit => "explicit"
  | Output.broad => "broad"

def showInput (i : Input) : String :=
  s!"refusal={i.refusal} launch={i.launch} narrow={i.narrow} broad={i.broad}"

def showOutput (o : Output) : String := encodeOutput o

end HP
