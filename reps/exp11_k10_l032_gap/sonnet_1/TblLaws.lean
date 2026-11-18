/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Leaf0 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = false → c.b6 = false → c.b7 = false → f c = true
def Leaf1 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = false → c.b6 = false → c.b7 = true → c.b0 = false → f c = false
def Leaf2 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = false → c.b6 = false → c.b7 = true → c.b0 = true → f c = true
def Leaf3 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = false → c.b6 = true → f c = false
def Leaf4 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = true → c.b0 = false → c.b7 = false → c.b5 = false → f c = false
def Leaf5 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = true → c.b0 = false → c.b7 = false → c.b5 = true → f c = true
def Leaf6 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = true → c.b0 = false → c.b7 = true → f c = true
def Leaf7 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = false → c.b9 = true → c.b0 = true → f c = true
def Leaf8 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = false → c.b3 = true → f c = false
def Leaf9 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = false → c.b8 = false → c.b6 = false → f c = false
def Leaf10 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = false → c.b8 = false → c.b6 = true → f c = false
def Leaf11 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = false → c.b8 = true → c.b6 = false → c.b9 = false → f c = true
def Leaf12 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = false → c.b8 = true → c.b6 = false → c.b9 = true → c.b4 = false → c.b5 = false → f c = false
def Leaf13 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = false → c.b8 = true → c.b6 = false → c.b9 = true → c.b4 = false → c.b5 = true → f c = true
def Leaf14 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = false → c.b8 = true → c.b6 = false → c.b9 = true → c.b4 = true → f c = false
def Leaf15 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = false → c.b8 = true → c.b6 = true → f c = false
def Leaf16 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = true → c.b3 = false → f c = false
def Leaf17 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = true → c.b3 = true → c.b9 = false → f c = false
def Leaf18 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b0 = true → c.b3 = true → c.b9 = true → f c = true
def Leaf19 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = false → c.b3 = false → c.b7 = false → f c = false
def Leaf20 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = false → c.b3 = false → c.b7 = true → f c = true
def Leaf21 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = false → c.b3 = true → c.b7 = false → f c = true
def Leaf22 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = false → c.b3 = true → c.b7 = true → f c = false
def Leaf23 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = true → c.b4 = false → c.b5 = false → f c = true
def Leaf24 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = true → c.b4 = false → c.b5 = true → f c = true
def Leaf26 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = true → c.b4 = true → c.b7 = false → c.b0 = true → f c = false
def Leaf27 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = false → c.b9 = true → c.b4 = true → c.b7 = true → f c = false
def Leaf28 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = true → c.b5 = false → c.b3 = false → f c = true
def Leaf29 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = true → c.b5 = false → c.b3 = true → f c = true
def Leaf30 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b8 = true → c.b5 = true → f c = true
def Leaf31 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = true → f c = false

/-- A rule passes when each law holds for it. -/
def Passes (f : Decide) : Prop :=
  Leaf0 f ∧
  Leaf1 f ∧
  Leaf2 f ∧
  Leaf3 f ∧
  Leaf4 f ∧
  Leaf5 f ∧
  Leaf6 f ∧
  Leaf7 f ∧
  Leaf8 f ∧
  Leaf9 f ∧
  Leaf10 f ∧
  Leaf11 f ∧
  Leaf12 f ∧
  Leaf13 f ∧
  Leaf14 f ∧
  Leaf15 f ∧
  Leaf16 f ∧
  Leaf17 f ∧
  Leaf18 f ∧
  Leaf19 f ∧
  Leaf20 f ∧
  Leaf21 f ∧
  Leaf22 f ∧
  Leaf23 f ∧
  Leaf24 f ∧
  Leaf26 f ∧
  Leaf27 f ∧
  Leaf28 f ∧
  Leaf29 f ∧
  Leaf30 f ∧
  Leaf31 f

end Tbl
