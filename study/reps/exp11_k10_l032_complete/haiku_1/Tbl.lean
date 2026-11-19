/-
Hard Proof, experiment 11. GENERATED FILE (human-owned).

A decision-table domain: 10 boolean inputs, a rule with 32 leaves. Seed 1.
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

/-- The reference rule. -/
def ref : Decide := fun c =>
  (if c.b2 then (if c.b6 then false else (if c.b8 then (if c.b5 then true else (if c.b3 then true else true)) else (if c.b9 then (if c.b4 then (if c.b7 then false else (if c.b0 then false else true)) else (if c.b5 then true else true)) else (if c.b3 then (if c.b7 then false else true) else (if c.b7 then true else false))))) else (if c.b1 then (if c.b0 then (if c.b3 then (if c.b9 then true else false) else false) else (if c.b8 then (if c.b6 then false else (if c.b9 then (if c.b4 then false else (if c.b5 then true else false)) else true)) else (if c.b6 then false else false))) else (if c.b3 then false else (if c.b9 then (if c.b0 then true else (if c.b7 then true else (if c.b5 then true else false))) else (if c.b6 then false else (if c.b7 then (if c.b0 then true else false) else true))))))

end Tbl
