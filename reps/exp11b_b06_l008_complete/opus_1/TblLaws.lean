/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Law0 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b0 = true → c.b4 = true → c.b2 = false → c.b5 = false → f c = false
def Law1 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b5 = true → c.b2 = false → c.b4 = true → f c = false
def Law2 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b3 = false → c.b4 = true → c.b2 = false → c.b0 = true → f c = false
def Law3 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b4 = false → c.b0 = true → c.b5 = false → f c = false
def Law4 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b5 = true → c.b4 = false → c.b2 = false → c.b0 = true → f c = false
def Law5 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b1 = true → c.b4 = false → c.b2 = false → c.b0 = true → f c = false
def Law6 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → f c = true
def Law7 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b2 = true → f c = true



/-- A rule passes when each law holds for it. -/
def Passes (f : Decide) : Prop :=
  Law0 f ∧
  Law1 f ∧
  Law2 f ∧
  Law3 f ∧
  Law4 f ∧
  Law5 f ∧
  Law6 f ∧
  Law7 f

end Tbl
