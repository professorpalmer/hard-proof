/-
Hard Proof, experiment 11. GENERATED FILE (human-owned).

A decision-table domain: 6 boolean inputs, a rule with 8 leaves. Seed 1.
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
deriving DecidableEq, Repr

/-- A rule: one answer for each case. -/
abbrev Decide := Case → Bool

/-- The reference rule. -/
def ref : Decide := fun c =>
  (if c.b1 then (if c.b4 then (if c.b3 then true else false) else false) else (if c.b0 then (if c.b5 then false else true) else (if c.b2 then true else (if c.b4 then true else true))))

end Tbl
