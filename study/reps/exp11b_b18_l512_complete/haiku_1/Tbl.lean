/-
Hard Proof, experiment 11. GENERATED FILE (human-owned).

A decision-table domain: 18 boolean inputs, a rule with 512 leaves. Seed 2.
-/

namespace Tbl

/-- The inputs of one decision. -/
structure Case where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b9 : Bool
  b10 : Bool
  b11 : Bool
  b12 : Bool
  b13 : Bool
  b14 : Bool
  b15 : Bool
  b16 : Bool
  b17 : Bool
deriving DecidableEq, Repr

/-- A rule: one answer for each case. -/
abbrev Decide := Case → Bool

end Tbl
