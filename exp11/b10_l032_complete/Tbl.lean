/-
Hard Proof, experiment 11. GENERATED FILE (human-owned).

A decision-table domain: 10 boolean inputs, a rule with 32 leaves. Seed 2.
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
deriving DecidableEq, Repr

/-- A rule: one answer for each case. -/
abbrev Decide := Case → Bool

end Tbl
