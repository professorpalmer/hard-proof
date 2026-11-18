/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Leaf0 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b0 = false → c.b2 = false → c.b4 = false → f c = true
def Leaf1 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b0 = false → c.b2 = false → c.b4 = true → f c = true
def Leaf2 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b0 = false → c.b2 = true → f c = true
def Leaf3 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b0 = true → c.b5 = false → f c = true
def Leaf4 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b0 = true → c.b5 = true → f c = false
def Leaf5 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b4 = false → f c = false
def Leaf6 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b4 = true → c.b3 = false → f c = false
def Leaf7 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b4 = true → c.b3 = true → f c = true

/-- A rule passes when each law holds for it. -/
def Passes (f : Decide) : Prop :=
  Leaf0 f ∧
  Leaf1 f ∧
  Leaf2 f ∧
  Leaf3 f ∧
  Leaf4 f ∧
  Leaf5 f ∧
  Leaf6 f ∧
  Leaf7 f

end Tbl
