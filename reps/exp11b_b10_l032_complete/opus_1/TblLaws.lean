/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Law0 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b1 = false → c.b6 = false → c.b0 = true → c.b7 = true → c.b5 = true → c.b3 = false → c.b4 = false → f c = false
def Law1 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b9 = false → c.b2 = false → c.b8 = true → c.b7 = false → c.b4 = false → c.b3 = false → c.b5 = true → c.b0 = true → c.b6 = false → f c = false
def Law2 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b0 = false → f c = true
def Law3 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b4 = true → c.b3 = true → c.b0 = true → c.b9 = true → f c = true
def Law4 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b1 = false → c.b8 = true → c.b0 = true → c.b7 = false → c.b3 = true → c.b5 = true → f c = false
def Law5 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b1 = false → c.b8 = true → c.b0 = true → c.b5 = true → c.b7 = false → c.b9 = false → c.b6 = false → c.b2 = true → c.b4 = false → f c = false
def Law6 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b8 = true → c.b0 = true → c.b1 = false → c.b6 = false → c.b5 = false → c.b4 = false → f c = true
def Law7 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b9 = true → c.b0 = true → c.b4 = true → f c = true
def Law8 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b7 = false → c.b4 = false → c.b0 = true → c.b1 = false → c.b8 = false → f c = true
def Law9 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b4 = false → c.b2 = true → c.b5 = false → c.b3 = false → c.b8 = true → c.b9 = false → c.b6 = true → c.b1 = false → f c = false
def Law10 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b1 = false → c.b8 = false → c.b0 = true → c.b7 = false → c.b9 = false → c.b4 = false → f c = false
def Law11 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b2 = false → c.b4 = false → f c = false
def Law12 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b0 = true → c.b6 = true → c.b1 = false → c.b5 = true → c.b3 = false → c.b4 = false → f c = false
def Law13 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b8 = false → c.b0 = true → c.b5 = false → c.b9 = false → c.b4 = true → c.b6 = false → c.b2 = false → f c = false
def Law14 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b4 = false → c.b0 = true → c.b8 = true → c.b1 = false → c.b3 = true → f c = true
def Law15 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b6 = true → c.b0 = true → c.b4 = false → c.b3 = false → c.b8 = true → c.b1 = false → c.b5 = false → f c = false
def Law16 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b5 = false → c.b6 = true → c.b1 = false → c.b3 = true → c.b8 = true → c.b4 = false → c.b0 = true → f c = false
def Law17 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b8 = false → c.b1 = false → c.b4 = false → c.b2 = true → c.b0 = true → c.b9 = true → f c = false
def Law18 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b1 = false → c.b2 = true → c.b0 = true → c.b9 = true → c.b8 = true → c.b5 = false → c.b3 = false → c.b6 = true → f c = false
def Law19 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b6 = false → c.b0 = true → c.b8 = false → c.b4 = false → c.b7 = true → c.b1 = false → f c = false
def Law20 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b1 = false → c.b0 = true → c.b8 = true → c.b5 = false → c.b3 = true → c.b6 = false → c.b4 = false → f c = false
def Law21 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b9 = true → c.b2 = false → c.b0 = true → c.b4 = false → c.b1 = false → c.b8 = false → f c = true
def Law22 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b1 = true → c.b0 = true → f c = false
def Law23 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b1 = false → c.b6 = true → c.b8 = false → c.b4 = false → c.b0 = true → f c = false
def Law24 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b9 = false → c.b8 = true → c.b0 = true → c.b6 = false → f c = true
def Law25 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b9 = false → c.b5 = false → c.b6 = false → c.b4 = true → c.b8 = false → c.b0 = true → f c = false
def Law26 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b9 = false → c.b6 = false → c.b8 = false → c.b0 = true → c.b5 = true → f c = false
def Law27 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b9 = true → c.b4 = true → c.b8 = false → c.b0 = true → f c = false
def Law28 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b9 = true → c.b7 = false → c.b1 = false → c.b0 = true → c.b3 = false → c.b8 = true → c.b4 = false → c.b5 = true → f c = true
def Law29 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b8 = false → c.b7 = true → c.b0 = true → c.b5 = false → c.b6 = false → c.b9 = false → c.b2 = false → f c = false
def Law30 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b0 = false → c.b4 = true → f c = false
def Law31 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b6 = true → c.b4 = true → c.b0 = true → f c = true



/-- A rule passes when each law holds for it. -/
def Passes (f : Decide) : Prop :=
  Law0 f ∧
  Law1 f ∧
  Law2 f ∧
  Law3 f ∧
  Law4 f ∧
  Law5 f ∧
  Law6 f ∧
  Law7 f ∧
  Law8 f ∧
  Law9 f ∧
  Law10 f ∧
  Law11 f ∧
  Law12 f ∧
  Law13 f ∧
  Law14 f ∧
  Law15 f ∧
  Law16 f ∧
  Law17 f ∧
  Law18 f ∧
  Law19 f ∧
  Law20 f ∧
  Law21 f ∧
  Law22 f ∧
  Law23 f ∧
  Law24 f ∧
  Law25 f ∧
  Law26 f ∧
  Law27 f ∧
  Law28 f ∧
  Law29 f ∧
  Law30 f ∧
  Law31 f

end Tbl
