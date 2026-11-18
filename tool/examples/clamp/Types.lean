/-
hardproof domain `clamp`. AUTHOR FILE (pinned).

The input is three integers. The output is one integer.
-/

namespace HP

/-- The arguments of `clamp(x, lo, hi)`. -/
structure Input where
  x : Int
  lo : Int
  hi : Int
deriving DecidableEq, Repr

/-- The return value of `clamp`. -/
abbrev Output := Int

/-- A design of `clamp`. -/
abbrev Impl := Input → Output

/-- A legal call has `lo ≤ hi`. -/
def legal (i : Input) : Bool := decide (i.lo ≤ i.hi)

def Legal (i : Input) : Prop := legal i = true

end HP
