/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Leaf0 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = false → c.b13 = false → c.b3 = false → c.b17 = false → c.b14 = false → f c = false
def Leaf1 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = false → c.b13 = false → c.b3 = false → c.b17 = false → c.b14 = true → f c = false
def Leaf2 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = false → c.b13 = false → c.b3 = false → c.b17 = true → f c = true
def Leaf3 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = false → c.b13 = false → c.b3 = true → f c = true
def Leaf4 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = false → c.b13 = true → c.b3 = false → f c = false
def Leaf5 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = false → c.b13 = true → c.b3 = true → c.b6 = false → f c = false
def Leaf6 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = false → c.b13 = true → c.b3 = true → c.b6 = true → f c = true
def Leaf7 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = false → c.b0 = true → f c = true
def Leaf8 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = true → c.b12 = false → f c = false
def Leaf9 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = true → c.b12 = true → c.b14 = false → c.b17 = false → f c = true
def Leaf10 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = true → c.b12 = true → c.b14 = false → c.b17 = true → c.b7 = false → c.b6 = false → f c = false
def Leaf11 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = true → c.b12 = true → c.b14 = false → c.b17 = true → c.b7 = false → c.b6 = true → f c = true
def Leaf12 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = true → c.b12 = true → c.b14 = false → c.b17 = true → c.b7 = true → f c = false
def Leaf13 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = false → c.b1 = true → c.b12 = true → c.b14 = true → f c = false
def Leaf14 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = false → c.b17 = false → c.b3 = false → c.b16 = false → f c = false
def Leaf15 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = false → c.b17 = false → c.b3 = false → c.b16 = true → f c = true
def Leaf16 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = false → c.b17 = false → c.b3 = true → f c = false
def Leaf17 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = false → c.b17 = true → c.b7 = false → c.b11 = false → f c = false
def Leaf18 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = false → c.b17 = true → c.b7 = false → c.b11 = true → f c = false
def Leaf19 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = false → c.b17 = true → c.b7 = true → f c = false
def Leaf20 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = false → f c = true
def Leaf21 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = false → c.b6 = false → c.b11 = false → c.b0 = false → f c = true
def Leaf22 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = false → c.b6 = false → c.b11 = false → c.b0 = true → f c = false
def Leaf23 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = false → c.b6 = false → c.b11 = true → f c = false
def Leaf24 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = false → c.b6 = true → c.b11 = false → c.b7 = false → f c = true
def Leaf25 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = false → c.b6 = true → c.b11 = false → c.b7 = true → f c = true
def Leaf26 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = false → c.b6 = true → c.b11 = true → c.b0 = false → f c = true
def Leaf27 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = false → c.b6 = true → c.b11 = true → c.b0 = true → f c = false
def Leaf28 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = true → c.b13 = false → c.b3 = false → f c = false
def Leaf29 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = true → c.b13 = false → c.b3 = true → f c = false
def Leaf30 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = true → c.b13 = true → c.b16 = false → f c = false
def Leaf31 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = true → c.b13 = true → c.b16 = true → c.b8 = false → f c = true
def Leaf32 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = false → c.b17 = true → c.b12 = true → c.b13 = true → c.b16 = true → c.b8 = true → f c = false
def Leaf33 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = false → c.b13 = false → c.b0 = false → c.b16 = false → f c = false
def Leaf34 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = false → c.b13 = false → c.b0 = false → c.b16 = true → f c = false
def Leaf35 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = false → c.b13 = false → c.b0 = true → f c = false
def Leaf36 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = false → c.b13 = true → c.b6 = false → f c = true
def Leaf37 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = false → c.b13 = true → c.b6 = true → c.b0 = false → f c = true
def Leaf38 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = false → c.b13 = true → c.b6 = true → c.b0 = true → f c = true
def Leaf39 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = true → c.b16 = false → f c = false
def Leaf40 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = true → c.b16 = true → c.b12 = false → f c = true
def Leaf41 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b1 = true → c.b14 = true → c.b17 = true → c.b16 = true → c.b12 = true → f c = true
def Leaf42 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = false → f c = false
def Leaf43 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = false → c.b12 = false → c.b0 = false → c.b6 = false → f c = false
def Leaf44 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = false → c.b12 = false → c.b0 = false → c.b6 = true → f c = true
def Leaf45 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = false → c.b12 = false → c.b0 = true → c.b3 = false → c.b1 = false → f c = false
def Leaf46 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = false → c.b12 = false → c.b0 = true → c.b3 = false → c.b1 = true → f c = false
def Leaf47 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = false → c.b12 = false → c.b0 = true → c.b3 = true → f c = true
def Leaf48 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = false → c.b12 = true → f c = true
def Leaf49 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = true → c.b0 = false → c.b7 = false → c.b3 = false → f c = false
def Leaf50 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = true → c.b0 = false → c.b7 = false → c.b3 = true → f c = true
def Leaf51 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = true → c.b0 = false → c.b7 = true → f c = true
def Leaf52 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = true → c.b0 = true → c.b6 = false → f c = true
def Leaf53 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = true → c.b0 = true → c.b6 = true → c.b7 = false → c.b13 = false → f c = false
def Leaf54 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = true → c.b0 = true → c.b6 = true → c.b7 = false → c.b13 = true → f c = true
def Leaf55 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = false → c.b16 = true → c.b0 = true → c.b6 = true → c.b7 = true → f c = true
def Leaf56 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = true → c.b12 = false → f c = true
def Leaf57 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = false → c.b10 = true → c.b8 = true → c.b14 = true → c.b12 = true → f c = true
def Leaf58 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = false → c.b9 = false → f c = false
def Leaf59 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = false → c.b9 = true → f c = false
def Leaf60 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = false → f c = true
def Leaf61 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = false → c.b0 = false → f c = true
def Leaf62 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = false → c.b0 = true → c.b11 = false → f c = false
def Leaf63 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = false → c.b0 = true → c.b11 = true → f c = false
def Leaf64 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = true → c.b9 = false → c.b10 = false → c.b14 = false → f c = false
def Leaf65 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = true → c.b9 = false → c.b10 = false → c.b14 = true → f c = true
def Leaf66 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = true → c.b9 = false → c.b10 = true → c.b14 = false → c.b11 = false → f c = true
def Leaf67 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = true → c.b9 = false → c.b10 = true → c.b14 = false → c.b11 = true → f c = true
def Leaf68 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = true → c.b9 = false → c.b10 = true → c.b14 = true → f c = false
def Leaf69 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = false → c.b12 = true → c.b13 = true → c.b9 = true → f c = false
def Leaf70 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = false → c.b7 = true → c.b6 = true → f c = true
def Leaf71 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = false → c.b12 = false → c.b10 = false → c.b0 = false → f c = false
def Leaf72 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = false → c.b12 = false → c.b10 = false → c.b0 = true → f c = false
def Leaf73 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = false → c.b12 = false → c.b10 = true → c.b7 = false → c.b3 = false → f c = false
def Leaf74 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = false → c.b12 = false → c.b10 = true → c.b7 = false → c.b3 = true → f c = false
def Leaf75 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = false → c.b12 = false → c.b10 = true → c.b7 = true → f c = false
def Leaf76 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = false → c.b12 = true → f c = false
def Leaf77 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = false → c.b10 = false → c.b6 = false → f c = false
def Leaf78 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = false → c.b10 = false → c.b6 = true → c.b12 = false → f c = false
def Leaf79 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = false → c.b10 = false → c.b6 = true → c.b12 = true → f c = true
def Leaf80 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = false → c.b10 = true → c.b14 = false → c.b12 = false → f c = true
def Leaf81 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = false → c.b10 = true → c.b14 = false → c.b12 = true → f c = true
def Leaf82 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = false → c.b10 = true → c.b14 = true → c.b16 = false → f c = true
def Leaf83 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = false → c.b10 = true → c.b14 = true → c.b16 = true → f c = true
def Leaf84 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = true → c.b7 = false → c.b13 = false → f c = false
def Leaf85 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = true → c.b7 = false → c.b13 = true → f c = false
def Leaf86 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = true → c.b7 = true → c.b10 = false → c.b12 = false → f c = true
def Leaf87 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = true → c.b7 = true → c.b10 = false → c.b12 = true → c.b3 = false → f c = false
def Leaf88 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = true → c.b7 = true → c.b10 = false → c.b12 = true → c.b3 = true → f c = false
def Leaf89 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = true → c.b7 = true → c.b10 = true → c.b11 = false → f c = false
def Leaf90 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = false → c.b9 = true → c.b0 = true → c.b7 = true → c.b10 = true → c.b11 = true → f c = false
def Leaf91 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = false → c.b3 = false → c.b0 = false → f c = true
def Leaf92 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = false → c.b3 = false → c.b0 = true → c.b7 = false → f c = false
def Leaf93 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = false → c.b3 = false → c.b0 = true → c.b7 = true → f c = true
def Leaf94 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = false → c.b3 = true → f c = false
def Leaf95 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = false → c.b10 = false → c.b6 = false → f c = true
def Leaf96 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = false → c.b10 = false → c.b6 = true → c.b11 = false → f c = false
def Leaf97 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = false → c.b10 = false → c.b6 = true → c.b11 = true → f c = false
def Leaf98 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = false → c.b10 = true → c.b7 = false → f c = true
def Leaf99 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = false → c.b10 = true → c.b7 = true → f c = false
def Leaf100 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = true → c.b3 = false → c.b0 = false → c.b6 = false → f c = true
def Leaf101 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = true → c.b3 = false → c.b0 = false → c.b6 = true → f c = false
def Leaf102 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = true → c.b3 = false → c.b0 = true → f c = true
def Leaf103 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = true → c.b3 = true → c.b6 = false → c.b0 = false → f c = false
def Leaf104 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = true → c.b3 = true → c.b6 = false → c.b0 = true → f c = false
def Leaf105 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = true → c.b3 = true → c.b6 = true → c.b10 = false → f c = true
def Leaf106 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = false → c.b14 = true → c.b16 = true → c.b3 = true → c.b6 = true → c.b10 = true → f c = false
def Leaf107 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = true → c.b16 = false → f c = false
def Leaf108 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = true → c.b16 = true → c.b10 = false → c.b3 = false → f c = true
def Leaf109 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = true → c.b16 = true → c.b10 = false → c.b3 = true → f c = true
def Leaf110 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = true → c.b16 = true → c.b10 = true → c.b0 = false → f c = false
def Leaf111 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = false → c.b17 = true → c.b1 = true → c.b13 = true → c.b16 = true → c.b10 = true → c.b0 = true → f c = true
def Leaf112 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = false → f c = true
def Leaf113 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = false → c.b9 = false → c.b13 = false → f c = true
def Leaf114 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = false → c.b9 = false → c.b13 = true → c.b7 = false → f c = false
def Leaf115 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = false → c.b9 = false → c.b13 = true → c.b7 = true → f c = true
def Leaf116 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = false → c.b9 = true → f c = false
def Leaf117 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = false → c.b17 = false → c.b10 = false → c.b7 = false → f c = true
def Leaf118 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = false → c.b17 = false → c.b10 = false → c.b7 = true → f c = false
def Leaf119 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = false → c.b17 = false → c.b10 = true → f c = true
def Leaf120 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = false → c.b17 = true → c.b3 = false → c.b13 = false → f c = false
def Leaf121 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = false → c.b17 = true → c.b3 = false → c.b13 = true → f c = true
def Leaf122 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = false → c.b17 = true → c.b3 = true → c.b9 = false → f c = true
def Leaf123 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = false → c.b17 = true → c.b3 = true → c.b9 = true → f c = true
def Leaf124 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = true → c.b11 = false → f c = false
def Leaf125 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = false → c.b0 = true → c.b12 = true → c.b11 = true → f c = false
def Leaf126 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = false → c.b15 = true → c.b8 = true → c.b14 = true → c.b1 = true → f c = true
def Leaf127 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = true → c.b6 = false → c.b16 = false → c.b14 = false → f c = true
def Leaf128 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = true → c.b6 = false → c.b16 = false → c.b14 = true → f c = true
def Leaf129 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = true → c.b6 = false → c.b16 = true → f c = true
def Leaf130 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b5 = true → c.b6 = true → f c = true
def Leaf131 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = false → c.b14 = false → c.b7 = false → c.b9 = false → f c = true
def Leaf132 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = false → c.b14 = false → c.b7 = false → c.b9 = true → f c = true
def Leaf133 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = false → c.b14 = false → c.b7 = true → f c = false
def Leaf134 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = false → c.b14 = true → c.b15 = false → c.b7 = false → f c = true
def Leaf135 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = false → c.b14 = true → c.b15 = false → c.b7 = true → f c = false
def Leaf136 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = false → c.b14 = true → c.b15 = true → f c = false
def Leaf137 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = true → c.b14 = false → f c = true
def Leaf138 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = false → c.b3 = true → c.b14 = true → f c = true
def Leaf139 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = false → c.b1 = true → f c = false
def Leaf140 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = false → c.b6 = false → f c = false
def Leaf141 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = false → c.b6 = true → f c = true
def Leaf142 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = false → f c = false
def Leaf143 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = false → c.b12 = false → c.b5 = false → f c = false
def Leaf144 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = false → c.b12 = false → c.b5 = true → c.b11 = false → f c = false
def Leaf145 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = false → c.b12 = false → c.b5 = true → c.b11 = true → c.b6 = false → f c = true
def Leaf146 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = false → c.b12 = false → c.b5 = true → c.b11 = true → c.b6 = true → f c = true
def Leaf147 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = false → c.b12 = true → c.b5 = false → f c = false
def Leaf148 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = false → c.b12 = true → c.b5 = true → f c = true
def Leaf149 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = true → c.b3 = false → c.b6 = false → f c = false
def Leaf150 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = true → c.b3 = false → c.b6 = true → f c = true
def Leaf151 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = false → c.b16 = true → c.b8 = true → c.b1 = true → c.b7 = true → c.b3 = true → f c = false
def Leaf152 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = false → f c = false
def Leaf153 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = false → c.b14 = false → f c = false
def Leaf154 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = false → c.b14 = true → c.b9 = false → f c = false
def Leaf155 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = false → c.b14 = true → c.b9 = true → f c = false
def Leaf156 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = true → c.b11 = false → c.b12 = false → c.b1 = false → f c = true
def Leaf157 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = true → c.b11 = false → c.b12 = false → c.b1 = true → f c = true
def Leaf158 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = true → c.b11 = false → c.b12 = true → c.b7 = false → f c = true
def Leaf159 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = true → c.b11 = false → c.b12 = true → c.b7 = true → f c = false
def Leaf160 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = false → c.b6 = true → c.b8 = true → c.b11 = true → f c = false
def Leaf161 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = false → c.b10 = true → f c = false
def Leaf162 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = false → c.b10 = false → f c = false
def Leaf163 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = false → c.b10 = true → f c = false
def Leaf164 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = false → c.b10 = false → c.b11 = false → c.b6 = false → f c = false
def Leaf165 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = false → c.b10 = false → c.b11 = false → c.b6 = true → f c = true
def Leaf166 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = false → c.b10 = false → c.b11 = true → c.b3 = false → f c = true
def Leaf167 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = false → c.b10 = false → c.b11 = true → c.b3 = true → f c = true
def Leaf168 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = false → c.b10 = true → f c = false
def Leaf169 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = false → c.b6 = false → c.b10 = false → f c = false
def Leaf170 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = false → c.b6 = false → c.b10 = true → f c = false
def Leaf171 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = false → c.b6 = true → c.b12 = false → f c = true
def Leaf172 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = false → c.b6 = true → c.b12 = true → f c = false
def Leaf173 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = true → c.b11 = false → c.b12 = false → f c = true
def Leaf174 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = true → c.b11 = false → c.b12 = true → c.b3 = false → f c = false
def Leaf175 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = true → c.b11 = false → c.b12 = true → c.b3 = true → f c = false
def Leaf176 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = true → c.b11 = true → c.b8 = false → f c = false
def Leaf177 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = true → c.b11 = true → c.b8 = true → c.b6 = false → f c = true
def Leaf178 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = false → c.b5 = true → c.b1 = true → c.b7 = true → c.b14 = true → c.b11 = true → c.b8 = true → c.b6 = true → f c = false
def Leaf179 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = false → c.b9 = false → c.b10 = false → c.b6 = false → f c = true
def Leaf180 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = false → c.b9 = false → c.b10 = false → c.b6 = true → f c = true
def Leaf181 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = false → c.b9 = false → c.b10 = true → f c = false
def Leaf182 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = false → c.b9 = true → f c = false
def Leaf183 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = false → f c = true
def Leaf184 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = false → c.b6 = false → c.b10 = false → f c = false
def Leaf185 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = false → c.b6 = false → c.b10 = true → c.b1 = false → c.b9 = false → f c = true
def Leaf186 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = false → c.b6 = false → c.b10 = true → c.b1 = false → c.b9 = true → f c = false
def Leaf187 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = false → c.b6 = false → c.b10 = true → c.b1 = true → c.b9 = false → f c = false
def Leaf188 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = false → c.b6 = false → c.b10 = true → c.b1 = true → c.b9 = true → f c = false
def Leaf189 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = false → c.b6 = true → c.b10 = false → f c = false
def Leaf190 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = false → c.b6 = true → c.b10 = true → f c = true
def Leaf191 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = true → c.b6 = false → c.b9 = false → c.b1 = false → f c = false
def Leaf192 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = true → c.b6 = false → c.b9 = false → c.b1 = true → f c = true
def Leaf193 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = true → c.b6 = false → c.b9 = true → c.b10 = false → f c = false
def Leaf194 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = true → c.b6 = false → c.b9 = true → c.b10 = true → f c = true
def Leaf195 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = false → c.b7 = true → c.b6 = true → f c = false
def Leaf196 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = true → c.b9 = false → f c = false
def Leaf197 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = true → c.b9 = true → c.b7 = false → f c = true
def Leaf198 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = false → c.b3 = true → c.b14 = true → c.b8 = true → c.b9 = true → c.b7 = true → f c = false
def Leaf199 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = true → c.b1 = false → f c = false
def Leaf200 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = true → c.b1 = true → c.b9 = false → f c = true
def Leaf201 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = false → c.b12 = true → c.b1 = true → c.b9 = true → f c = false
def Leaf202 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = false → c.b5 = true → f c = false
def Leaf203 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = false → c.b5 = false → c.b6 = false → f c = true
def Leaf204 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = false → c.b5 = false → c.b6 = true → c.b10 = false → f c = false
def Leaf205 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = false → c.b5 = false → c.b6 = true → c.b10 = true → f c = false
def Leaf206 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = false → c.b5 = true → c.b14 = false → f c = false
def Leaf207 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = false → c.b5 = true → c.b14 = true → c.b8 = false → c.b1 = false → f c = false
def Leaf208 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = false → c.b5 = true → c.b14 = true → c.b8 = false → c.b1 = true → f c = false
def Leaf209 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = false → c.b5 = true → c.b14 = true → c.b8 = true → f c = true
def Leaf210 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = false → c.b1 = false → f c = true
def Leaf211 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = false → c.b1 = true → f c = false
def Leaf212 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = false → c.b1 = false → c.b12 = false → f c = false
def Leaf213 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = false → c.b1 = false → c.b12 = true → f c = true
def Leaf214 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = false → c.b1 = true → f c = false
def Leaf215 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = false → c.b5 = false → f c = true
def Leaf216 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = false → c.b5 = true → c.b10 = false → c.b6 = false → f c = false
def Leaf217 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = false → c.b5 = true → c.b10 = false → c.b6 = true → f c = true
def Leaf218 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = false → c.b5 = true → c.b10 = true → c.b12 = false → f c = true
def Leaf219 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = false → c.b5 = true → c.b10 = true → c.b12 = true → f c = false
def Leaf220 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = true → c.b6 = false → f c = false
def Leaf221 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = true → c.b6 = true → c.b5 = false → f c = false
def Leaf222 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = false → c.b15 = true → c.b11 = true → c.b7 = true → c.b8 = true → c.b9 = true → c.b14 = true → c.b6 = true → c.b5 = true → f c = false
def Leaf223 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = false → c.b10 = false → c.b12 = false → c.b7 = false → f c = false
def Leaf224 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = false → c.b10 = false → c.b12 = false → c.b7 = true → f c = true
def Leaf225 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = false → c.b10 = false → c.b12 = true → f c = false
def Leaf226 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = false → c.b10 = true → f c = true
def Leaf227 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = true → c.b11 = false → f c = false
def Leaf228 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = true → c.b11 = true → c.b14 = false → c.b9 = false → f c = true
def Leaf229 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = true → c.b11 = true → c.b14 = false → c.b9 = true → f c = false
def Leaf230 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = true → c.b11 = true → c.b14 = true → c.b3 = false → f c = true
def Leaf231 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = false → c.b16 = true → c.b15 = true → c.b11 = true → c.b14 = true → c.b3 = true → f c = false
def Leaf232 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = false → c.b17 = true → f c = false
def Leaf233 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = false → f c = true
def Leaf234 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = false → c.b17 = false → c.b7 = false → f c = false
def Leaf235 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = false → c.b17 = false → c.b7 = true → c.b1 = false → c.b9 = false → f c = false
def Leaf236 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = false → c.b17 = false → c.b7 = true → c.b1 = false → c.b9 = true → f c = true
def Leaf237 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = false → c.b17 = false → c.b7 = true → c.b1 = true → f c = false
def Leaf238 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = false → c.b17 = true → f c = true
def Leaf239 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = false → c.b11 = false → c.b12 = false → f c = false
def Leaf240 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = false → c.b11 = false → c.b12 = true → f c = true
def Leaf241 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = false → c.b11 = true → c.b3 = false → c.b5 = false → f c = true
def Leaf242 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = false → c.b11 = true → c.b3 = false → c.b5 = true → f c = false
def Leaf243 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = false → c.b11 = true → c.b3 = true → f c = true
def Leaf244 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = false → c.b5 = false → f c = true
def Leaf245 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = false → c.b5 = true → c.b8 = false → c.b3 = false → f c = true
def Leaf246 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = false → c.b5 = true → c.b8 = false → c.b3 = true → c.b7 = false → f c = true
def Leaf247 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = false → c.b5 = true → c.b8 = false → c.b3 = true → c.b7 = true → f c = true
def Leaf248 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = false → c.b5 = true → c.b8 = true → c.b17 = false → f c = false
def Leaf249 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = false → c.b5 = true → c.b8 = true → c.b17 = true → f c = false
def Leaf250 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = true → c.b11 = false → f c = false
def Leaf251 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b12 = true → c.b11 = true → f c = false
def Leaf252 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = false → c.b11 = false → c.b12 = false → f c = true
def Leaf253 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = false → c.b11 = false → c.b12 = true → c.b6 = false → f c = false
def Leaf254 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = false → c.b11 = false → c.b12 = true → c.b6 = true → f c = true
def Leaf255 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = false → c.b11 = true → f c = true
def Leaf256 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = false → c.b1 = false → c.b10 = false → c.b11 = false → f c = false
def Leaf257 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = false → c.b1 = false → c.b10 = false → c.b11 = true → c.b6 = false → f c = true
def Leaf258 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = false → c.b1 = false → c.b10 = false → c.b11 = true → c.b6 = true → f c = false
def Leaf259 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = false → c.b1 = false → c.b10 = true → c.b12 = false → f c = true
def Leaf260 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = false → c.b1 = false → c.b10 = true → c.b12 = true → f c = false
def Leaf261 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = false → c.b1 = true → c.b12 = false → f c = true
def Leaf262 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = false → c.b1 = true → c.b12 = true → f c = false
def Leaf263 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = false → c.b17 = true → c.b7 = true → f c = true
def Leaf264 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = true → c.b6 = false → c.b7 = false → f c = false
def Leaf265 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = true → c.b6 = false → c.b7 = true → f c = true
def Leaf266 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = true → c.b6 = true → c.b10 = false → c.b9 = false → f c = true
def Leaf267 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = true → c.b6 = true → c.b10 = false → c.b9 = true → f c = true
def Leaf268 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = true → c.b6 = true → c.b10 = true → c.b11 = false → f c = true
def Leaf269 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b8 = true → c.b6 = true → c.b10 = true → c.b11 = true → f c = true
def Leaf270 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = true → c.b9 = false → f c = true
def Leaf271 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = false → c.b16 = true → c.b9 = true → f c = true
def Leaf272 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = false → c.b1 = false → f c = false
def Leaf273 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = false → c.b1 = true → f c = true
def Leaf274 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = false → c.b15 = false → f c = false
def Leaf275 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = false → c.b15 = true → f c = false
def Leaf276 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = false → c.b10 = false → f c = false
def Leaf277 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = false → c.b10 = true → c.b3 = false → f c = true
def Leaf278 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = false → c.b10 = true → c.b3 = true → c.b7 = false → c.b15 = false → f c = true
def Leaf279 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = false → c.b10 = true → c.b3 = true → c.b7 = false → c.b15 = true → f c = true
def Leaf280 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = false → c.b10 = true → c.b3 = true → c.b7 = true → c.b9 = false → f c = true
def Leaf281 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = false → c.b10 = true → c.b3 = true → c.b7 = true → c.b9 = true → f c = true
def Leaf282 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = true → c.b15 = false → f c = true
def Leaf283 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b11 = true → c.b15 = true → f c = false
def Leaf284 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = false → c.b3 = false → f c = false
def Leaf285 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = false → c.b3 = true → c.b1 = false → f c = false
def Leaf286 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = false → c.b3 = true → c.b1 = true → c.b12 = false → f c = true
def Leaf287 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = false → c.b3 = true → c.b1 = true → c.b12 = true → f c = true
def Leaf288 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = true → c.b10 = false → f c = true
def Leaf289 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = true → c.b10 = true → c.b16 = false → f c = false
def Leaf290 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = true → c.b10 = true → c.b16 = true → c.b1 = false → f c = true
def Leaf291 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = true → c.b13 = true → c.b0 = true → c.b14 = true → c.b5 = true → c.b6 = true → c.b8 = true → c.b17 = true → c.b11 = true → c.b10 = true → c.b16 = true → c.b1 = true → f c = true
def Leaf292 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = false → c.b0 = false → f c = false
def Leaf293 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = false → c.b0 = true → c.b13 = false → f c = true
def Leaf294 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = false → c.b0 = true → c.b13 = true → c.b8 = false → f c = true
def Leaf295 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = false → c.b0 = true → c.b13 = true → c.b8 = true → c.b7 = false → f c = true
def Leaf296 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = false → c.b0 = true → c.b13 = true → c.b8 = true → c.b7 = true → f c = false
def Leaf297 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = true → c.b16 = false → c.b15 = false → f c = false
def Leaf298 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = true → c.b16 = false → c.b15 = true → c.b9 = false → f c = true
def Leaf299 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = true → c.b16 = false → c.b15 = true → c.b9 = true → f c = true
def Leaf300 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = true → c.b16 = true → c.b7 = false → f c = true
def Leaf301 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = true → c.b16 = true → c.b7 = true → c.b15 = false → f c = false
def Leaf302 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = false → c.b10 = true → c.b16 = true → c.b7 = true → c.b15 = true → f c = false
def Leaf303 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = false → c.b9 = false → f c = false
def Leaf304 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = false → c.b9 = true → f c = false
def Leaf305 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = false → c.b6 = false → f c = true
def Leaf306 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = false → c.b6 = true → f c = true
def Leaf307 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = false → c.b10 = false → f c = false
def Leaf308 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = false → c.b10 = true → f c = true
def Leaf309 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = true → c.b5 = false → c.b17 = false → c.b6 = false → c.b7 = false → f c = true
def Leaf310 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = true → c.b5 = false → c.b17 = false → c.b6 = false → c.b7 = true → f c = true
def Leaf311 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = true → c.b5 = false → c.b17 = false → c.b6 = true → f c = false
def Leaf312 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = true → c.b5 = false → c.b17 = true → c.b7 = false → f c = false
def Leaf313 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = true → c.b5 = false → c.b17 = true → c.b7 = true → f c = false
def Leaf314 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = false → c.b11 = true → c.b0 = true → c.b5 = true → f c = true
def Leaf315 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = true → c.b11 = false → f c = false
def Leaf316 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = false → c.b9 = true → c.b11 = true → f c = true
def Leaf317 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = true → c.b10 = false → f c = true
def Leaf318 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = false → c.b2 = true → c.b10 = true → f c = true
def Leaf319 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = true → c.b10 = false → f c = false
def Leaf320 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b9 = false → c.b2 = false → c.b7 = false → f c = false
def Leaf321 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b9 = false → c.b2 = false → c.b7 = true → f c = false
def Leaf322 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b9 = false → c.b2 = true → f c = true
def Leaf323 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = false → c.b15 = true → c.b16 = true → c.b10 = true → c.b9 = true → f c = true
def Leaf324 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = true → c.b6 = false → f c = false
def Leaf325 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = false → c.b12 = true → c.b6 = true → f c = true
def Leaf326 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = true → c.b9 = false → c.b16 = false → c.b2 = false → f c = true
def Leaf327 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = true → c.b9 = false → c.b16 = false → c.b2 = true → f c = false
def Leaf328 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = true → c.b9 = false → c.b16 = true → c.b15 = false → f c = false
def Leaf329 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = true → c.b9 = false → c.b16 = true → c.b15 = true → f c = false
def Leaf330 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = false → c.b13 = true → c.b9 = true → f c = false
def Leaf331 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = false → f c = false
def Leaf332 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = false → c.b11 = false → c.b13 = false → f c = true
def Leaf333 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = false → c.b11 = false → c.b13 = true → f c = true
def Leaf334 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = false → c.b11 = true → c.b2 = false → f c = true
def Leaf335 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = false → c.b11 = true → c.b2 = true → f c = false
def Leaf336 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = false → c.b13 = false → c.b6 = false → f c = true
def Leaf337 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = false → c.b13 = false → c.b6 = true → f c = true
def Leaf338 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = false → c.b13 = true → f c = false
def Leaf339 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = true → c.b0 = false → f c = true
def Leaf340 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = true → c.b0 = true → c.b13 = false → c.b9 = false → f c = false
def Leaf341 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = true → c.b0 = true → c.b13 = false → c.b9 = true → f c = true
def Leaf342 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = true → c.b0 = true → c.b13 = true → c.b9 = false → f c = true
def Leaf343 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b17 = true → c.b0 = true → c.b13 = true → c.b9 = true → f c = false
def Leaf344 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = true → c.b11 = false → f c = false
def Leaf345 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = true → c.b11 = true → c.b0 = false → f c = true
def Leaf346 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = true → c.b11 = true → c.b0 = true → c.b17 = false → f c = false
def Leaf347 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = false → c.b12 = true → c.b7 = true → c.b11 = true → c.b0 = true → c.b17 = true → f c = false
def Leaf348 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = false → c.b10 = false → c.b12 = false → c.b15 = false → f c = false
def Leaf350 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = false → c.b10 = false → c.b12 = true → f c = false
def Leaf351 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = false → c.b10 = true → c.b0 = false → f c = true
def Leaf352 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = false → c.b10 = true → c.b0 = true → c.b9 = false → f c = false
def Leaf353 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = false → c.b10 = true → c.b0 = true → c.b9 = true → f c = false
def Leaf354 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = true → c.b5 = false → c.b17 = false → f c = true
def Leaf355 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = true → c.b5 = false → c.b17 = true → f c = true
def Leaf356 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = true → c.b5 = true → c.b15 = false → f c = false
def Leaf357 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = false → c.b3 = true → c.b8 = true → c.b16 = true → c.b6 = true → c.b5 = true → c.b15 = true → f c = false
def Leaf358 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = false → c.b3 = false → c.b16 = false → f c = false
def Leaf359 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = false → c.b3 = false → c.b16 = true → f c = false
def Leaf360 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = false → c.b3 = true → c.b11 = false → f c = false
def Leaf361 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = false → c.b3 = true → c.b11 = true → c.b13 = false → c.b8 = false → f c = false
def Leaf362 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = false → c.b3 = true → c.b11 = true → c.b13 = false → c.b8 = true → f c = false
def Leaf363 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = false → c.b3 = true → c.b11 = true → c.b13 = true → f c = false
def Leaf364 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = false → c.b13 = false → c.b6 = false → f c = false
def Leaf365 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = false → c.b13 = false → c.b6 = true → c.b15 = false → c.b0 = false → f c = true
def Leaf366 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = false → c.b13 = false → c.b6 = true → c.b15 = false → c.b0 = true → f c = false
def Leaf367 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = false → c.b13 = false → c.b6 = true → c.b15 = true → f c = false
def Leaf368 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = false → c.b13 = true → c.b15 = false → c.b0 = false → f c = true
def Leaf369 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = false → c.b13 = true → c.b15 = false → c.b0 = true → f c = false
def Leaf370 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = false → c.b13 = true → c.b15 = true → f c = true
def Leaf371 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = false → c.b3 = true → f c = false
def Leaf372 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = false → c.b8 = true → f c = false
def Leaf373 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = true → c.b0 = false → f c = false
def Leaf374 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = false → c.b10 = true → c.b0 = true → f c = false
def Leaf375 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = true → c.b15 = false → c.b16 = false → f c = false
def Leaf376 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = true → c.b15 = false → c.b16 = true → f c = false
def Leaf377 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = false → c.b12 = true → c.b15 = true → f c = true
def Leaf378 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = false → c.b17 = false → c.b9 = false → c.b10 = false → f c = false
def Leaf379 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = false → c.b17 = false → c.b9 = false → c.b10 = true → c.b12 = false → f c = false
def Leaf380 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = false → c.b17 = false → c.b9 = false → c.b10 = true → c.b12 = true → c.b3 = false → f c = true
def Leaf381 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = false → c.b17 = false → c.b9 = false → c.b10 = true → c.b12 = true → c.b3 = true → f c = true
def Leaf382 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = false → c.b17 = false → c.b9 = true → c.b13 = false → f c = false
def Leaf383 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = false → c.b17 = false → c.b9 = true → c.b13 = true → f c = false
def Leaf384 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = false → c.b17 = true → f c = true
def Leaf385 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = true → c.b12 = false → f c = true
def Leaf386 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = false → c.b15 = true → c.b12 = true → f c = false
def Leaf387 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = true → c.b17 = false → f c = false
def Leaf388 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = true → c.b17 = true → c.b3 = false → f c = true
def Leaf389 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = true → c.b17 = true → c.b3 = true → c.b15 = false → c.b12 = false → f c = false
def Leaf390 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = true → c.b17 = true → c.b3 = true → c.b15 = false → c.b12 = true → f c = false
def Leaf391 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = false → c.b2 = true → c.b7 = true → c.b11 = true → c.b17 = true → c.b3 = true → c.b15 = true → f c = false
def Leaf392 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = false → c.b11 = false → c.b3 = false → f c = true
def Leaf393 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = false → c.b11 = false → c.b3 = true → f c = true
def Leaf394 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = false → c.b11 = true → c.b3 = false → f c = false
def Leaf395 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = false → c.b11 = true → c.b3 = true → f c = true
def Leaf396 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = false → c.b12 = false → c.b6 = false → c.b2 = false → f c = false
def Leaf397 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = false → c.b12 = false → c.b6 = false → c.b2 = true → f c = true
def Leaf398 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = false → c.b12 = false → c.b6 = true → c.b13 = false → f c = false
def Leaf399 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = false → c.b12 = false → c.b6 = true → c.b13 = true → f c = true
def Leaf400 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = false → c.b12 = true → c.b2 = false → f c = false
def Leaf401 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = false → c.b12 = true → c.b2 = true → c.b6 = false → f c = false
def Leaf402 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = false → c.b12 = true → c.b2 = true → c.b6 = true → f c = true
def Leaf403 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = true → c.b6 = false → f c = true
def Leaf404 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = false → c.b11 = true → c.b6 = true → f c = false
def Leaf405 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = true → c.b13 = false → c.b0 = false → f c = true
def Leaf406 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = true → c.b13 = false → c.b0 = true → f c = false
def Leaf407 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = true → c.b13 = true → c.b0 = false → f c = false
def Leaf408 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = true → c.b13 = true → c.b0 = true → c.b7 = false → f c = true
def Leaf409 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = false → c.b10 = true → c.b13 = true → c.b0 = true → c.b7 = true → f c = false
def Leaf410 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = true → c.b2 = false → c.b6 = false → c.b12 = false → f c = true
def Leaf411 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = true → c.b2 = false → c.b6 = false → c.b12 = true → f c = false
def Leaf412 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = true → c.b2 = false → c.b6 = true → c.b0 = false → f c = false
def Leaf413 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = true → c.b2 = false → c.b6 = true → c.b0 = true → f c = false
def Leaf414 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = false → c.b8 = true → c.b2 = true → f c = true
def Leaf415 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = true → c.b11 = false → f c = false
def Leaf416 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = true → c.b11 = true → c.b8 = false → c.b15 = false → c.b2 = false → c.b16 = false → c.b0 = false → f c = true
def Leaf417 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = true → c.b11 = true → c.b8 = false → c.b15 = false → c.b2 = false → c.b16 = false → c.b0 = true → f c = false
def Leaf418 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = true → c.b11 = true → c.b8 = false → c.b15 = false → c.b2 = false → c.b16 = true → f c = false
def Leaf419 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = true → c.b11 = true → c.b8 = false → c.b15 = false → c.b2 = true → f c = true
def Leaf420 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = true → c.b11 = true → c.b8 = false → c.b15 = true → f c = true
def Leaf421 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = false → c.b17 = true → c.b3 = true → c.b11 = true → c.b8 = true → f c = false
def Leaf422 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = false → c.b11 = false → c.b16 = false → f c = true
def Leaf423 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = false → c.b11 = false → c.b16 = true → f c = true
def Leaf424 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = false → c.b11 = true → c.b0 = false → c.b8 = false → f c = true
def Leaf425 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = false → c.b11 = true → c.b0 = false → c.b8 = true → f c = false
def Leaf426 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = false → c.b11 = true → c.b0 = true → f c = true
def Leaf427 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = false → c.b15 = false → c.b8 = false → f c = false
def Leaf428 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = false → c.b15 = false → c.b8 = true → f c = true
def Leaf429 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = false → c.b15 = true → c.b6 = false → f c = true
def Leaf430 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = false → c.b15 = true → c.b6 = true → f c = true
def Leaf431 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = true → c.b17 = false → c.b0 = false → c.b13 = false → f c = true
def Leaf432 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = true → c.b17 = false → c.b0 = false → c.b13 = true → f c = true
def Leaf433 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = true → c.b17 = false → c.b0 = true → c.b10 = false → c.b16 = false → f c = true
def Leaf434 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = true → c.b17 = false → c.b0 = true → c.b10 = false → c.b16 = true → f c = true
def Leaf435 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = true → c.b17 = false → c.b0 = true → c.b10 = true → f c = true
def Leaf436 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = false → c.b14 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b2 = true → c.b17 = true → f c = true
def Leaf437 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = false → c.b16 = false → f c = true
def Leaf438 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = false → c.b16 = true → c.b13 = false → f c = true
def Leaf439 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = false → c.b16 = true → c.b13 = true → f c = true
def Leaf440 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = true → c.b5 = false → c.b8 = false → f c = false
def Leaf441 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = true → c.b5 = false → c.b8 = true → c.b2 = false → f c = false
def Leaf442 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = true → c.b5 = false → c.b8 = true → c.b2 = true → f c = false
def Leaf443 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = true → c.b5 = true → c.b8 = false → f c = false
def Leaf444 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = true → c.b5 = true → c.b8 = true → c.b12 = false → f c = true
def Leaf445 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = false → c.b9 = true → c.b5 = true → c.b8 = true → c.b12 = true → f c = true
def Leaf446 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = false → c.b0 = true → f c = true
def Leaf447 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = false → c.b17 = false → c.b9 = false → f c = false
def Leaf448 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = false → c.b17 = false → c.b9 = true → f c = false
def Leaf449 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = false → c.b17 = true → c.b10 = false → c.b16 = false → f c = false
def Leaf450 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = false → c.b17 = true → c.b10 = false → c.b16 = true → f c = true
def Leaf451 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = false → c.b17 = true → c.b10 = true → c.b2 = false → f c = true
def Leaf452 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = false → c.b17 = true → c.b10 = true → c.b2 = true → f c = true
def Leaf453 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = false → f c = true
def Leaf454 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = false → c.b12 = false → f c = true
def Leaf455 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = false → c.b12 = true → f c = true
def Leaf456 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = true → c.b0 = false → c.b3 = false → f c = true
def Leaf457 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = true → c.b0 = false → c.b3 = true → c.b13 = false → f c = true
def Leaf458 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = true → c.b0 = false → c.b3 = true → c.b13 = true → f c = false
def Leaf459 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = true → c.b0 = true → c.b12 = false → f c = false
def Leaf460 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = true → c.b0 = true → c.b12 = true → c.b10 = false → f c = false
def Leaf461 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = true → c.b0 = true → c.b12 = true → c.b10 = true → c.b13 = false → f c = false
def Leaf462 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = false → c.b17 = true → c.b2 = true → c.b0 = true → c.b12 = true → c.b10 = true → c.b13 = true → f c = true
def Leaf463 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = false → c.b16 = false → c.b13 = false → f c = false
def Leaf464 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = false → c.b16 = false → c.b13 = true → c.b15 = false → f c = false
def Leaf465 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = false → c.b16 = false → c.b13 = true → c.b15 = true → f c = false
def Leaf466 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = false → c.b16 = true → c.b13 = false → f c = true
def Leaf467 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = false → c.b16 = true → c.b13 = true → f c = true
def Leaf468 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = false → c.b2 = false → f c = true
def Leaf469 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = false → c.b2 = true → f c = true
def Leaf470 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = false → c.b13 = false → f c = true
def Leaf471 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = false → c.b13 = true → c.b8 = false → c.b12 = false → c.b2 = false → f c = true
def Leaf472 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = false → c.b13 = true → c.b8 = false → c.b12 = false → c.b2 = true → f c = true
def Leaf473 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = false → c.b13 = true → c.b8 = false → c.b12 = true → f c = true
def Leaf474 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = false → c.b13 = true → c.b8 = true → f c = false
def Leaf475 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = false → c.b14 = false → c.b16 = false → f c = false
def Leaf476 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = false → c.b14 = false → c.b16 = true → c.b12 = false → c.b0 = false → f c = true
def Leaf477 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = false → c.b14 = false → c.b16 = true → c.b12 = false → c.b0 = true → c.b2 = false → f c = false
def Leaf478 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = false → c.b14 = false → c.b16 = true → c.b12 = false → c.b0 = true → c.b2 = true → f c = false
def Leaf479 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = false → c.b14 = false → c.b16 = true → c.b12 = true → f c = true
def Leaf480 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = false → c.b14 = true → f c = false
def Leaf481 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = true → c.b8 = false → c.b12 = false → f c = true
def Leaf482 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = true → c.b8 = false → c.b12 = true → c.b16 = false → f c = false
def Leaf483 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = true → c.b8 = false → c.b12 = true → c.b16 = true → f c = true
def Leaf484 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = true → c.b8 = true → c.b16 = false → f c = true
def Leaf485 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = false → c.b3 = true → c.b15 = true → c.b13 = true → c.b8 = true → c.b16 = true → f c = true
def Leaf486 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = false → c.b5 = true → c.b9 = true → c.b17 = true → c.b10 = true → f c = false
def Leaf487 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = false → c.b0 = false → f c = false
def Leaf488 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = false → c.b0 = true → c.b17 = false → f c = true
def Leaf489 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = false → c.b0 = true → c.b17 = true → c.b14 = false → f c = true
def Leaf490 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = false → c.b0 = true → c.b17 = true → c.b14 = true → c.b12 = false → f c = false
def Leaf491 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = false → c.b0 = true → c.b17 = true → c.b14 = true → c.b12 = true → f c = true
def Leaf492 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = true → c.b9 = false → c.b12 = false → f c = false
def Leaf493 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = true → c.b9 = false → c.b12 = true → f c = true
def Leaf494 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = false → c.b11 = true → c.b6 = true → c.b15 = true → c.b9 = true → f c = true
def Leaf495 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = false → f c = false
def Leaf496 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = false → c.b13 = false → f c = true
def Leaf497 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = false → c.b13 = true → f c = false
def Leaf498 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = false → c.b13 = false → c.b16 = false → f c = true
def Leaf499 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = false → c.b13 = false → c.b16 = true → f c = false
def Leaf500 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = false → c.b13 = true → c.b11 = false → f c = true
def Leaf501 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = false → c.b13 = true → c.b11 = true → c.b2 = false → c.b15 = false → f c = false
def Leaf502 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = false → c.b13 = true → c.b11 = true → c.b2 = false → c.b15 = true → f c = true
def Leaf503 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = false → c.b13 = true → c.b11 = true → c.b2 = true → f c = false
def Leaf504 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = true → c.b2 = false → c.b13 = false → f c = true
def Leaf505 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = true → c.b2 = false → c.b13 = true → f c = true
def Leaf506 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b8 = true → c.b2 = true → f c = false
def Leaf507 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = true → c.b12 = false → c.b16 = false → f c = false
def Leaf508 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = true → c.b12 = false → c.b16 = true → f c = true
def Leaf509 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = true → c.b12 = true → c.b10 = false → f c = false
def Leaf510 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = true → c.b12 = true → c.b10 = true → c.b5 = false → f c = false
def Leaf511 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b1 = true → c.b7 = true → c.b0 = true → c.b17 = true → c.b9 = true → c.b12 = true → c.b10 = true → c.b5 = true → f c = false

def Group0 (f : Decide) : Prop :=
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
  Leaf15 f

def Group1 (f : Decide) : Prop :=
  Leaf16 f ∧
  Leaf17 f ∧
  Leaf18 f ∧
  Leaf19 f ∧
  Leaf20 f ∧
  Leaf21 f ∧
  Leaf22 f ∧
  Leaf23 f ∧
  Leaf24 f ∧
  Leaf25 f ∧
  Leaf26 f ∧
  Leaf27 f ∧
  Leaf28 f ∧
  Leaf29 f ∧
  Leaf30 f ∧
  Leaf31 f

def Group2 (f : Decide) : Prop :=
  Leaf32 f ∧
  Leaf33 f ∧
  Leaf34 f ∧
  Leaf35 f ∧
  Leaf36 f ∧
  Leaf37 f ∧
  Leaf38 f ∧
  Leaf39 f ∧
  Leaf40 f ∧
  Leaf41 f ∧
  Leaf42 f ∧
  Leaf43 f ∧
  Leaf44 f ∧
  Leaf45 f ∧
  Leaf46 f ∧
  Leaf47 f

def Group3 (f : Decide) : Prop :=
  Leaf48 f ∧
  Leaf49 f ∧
  Leaf50 f ∧
  Leaf51 f ∧
  Leaf52 f ∧
  Leaf53 f ∧
  Leaf54 f ∧
  Leaf55 f ∧
  Leaf56 f ∧
  Leaf57 f ∧
  Leaf58 f ∧
  Leaf59 f ∧
  Leaf60 f ∧
  Leaf61 f ∧
  Leaf62 f ∧
  Leaf63 f

def Group4 (f : Decide) : Prop :=
  Leaf64 f ∧
  Leaf65 f ∧
  Leaf66 f ∧
  Leaf67 f ∧
  Leaf68 f ∧
  Leaf69 f ∧
  Leaf70 f ∧
  Leaf71 f ∧
  Leaf72 f ∧
  Leaf73 f ∧
  Leaf74 f ∧
  Leaf75 f ∧
  Leaf76 f ∧
  Leaf77 f ∧
  Leaf78 f ∧
  Leaf79 f

def Group5 (f : Decide) : Prop :=
  Leaf80 f ∧
  Leaf81 f ∧
  Leaf82 f ∧
  Leaf83 f ∧
  Leaf84 f ∧
  Leaf85 f ∧
  Leaf86 f ∧
  Leaf87 f ∧
  Leaf88 f ∧
  Leaf89 f ∧
  Leaf90 f ∧
  Leaf91 f ∧
  Leaf92 f ∧
  Leaf93 f ∧
  Leaf94 f ∧
  Leaf95 f

def Group6 (f : Decide) : Prop :=
  Leaf96 f ∧
  Leaf97 f ∧
  Leaf98 f ∧
  Leaf99 f ∧
  Leaf100 f ∧
  Leaf101 f ∧
  Leaf102 f ∧
  Leaf103 f ∧
  Leaf104 f ∧
  Leaf105 f ∧
  Leaf106 f ∧
  Leaf107 f ∧
  Leaf108 f ∧
  Leaf109 f ∧
  Leaf110 f ∧
  Leaf111 f

def Group7 (f : Decide) : Prop :=
  Leaf112 f ∧
  Leaf113 f ∧
  Leaf114 f ∧
  Leaf115 f ∧
  Leaf116 f ∧
  Leaf117 f ∧
  Leaf118 f ∧
  Leaf119 f ∧
  Leaf120 f ∧
  Leaf121 f ∧
  Leaf122 f ∧
  Leaf123 f ∧
  Leaf124 f ∧
  Leaf125 f ∧
  Leaf126 f ∧
  Leaf127 f

def Group8 (f : Decide) : Prop :=
  Leaf128 f ∧
  Leaf129 f ∧
  Leaf130 f ∧
  Leaf131 f ∧
  Leaf132 f ∧
  Leaf133 f ∧
  Leaf134 f ∧
  Leaf135 f ∧
  Leaf136 f ∧
  Leaf137 f ∧
  Leaf138 f ∧
  Leaf139 f ∧
  Leaf140 f ∧
  Leaf141 f ∧
  Leaf142 f ∧
  Leaf143 f

def Group9 (f : Decide) : Prop :=
  Leaf144 f ∧
  Leaf145 f ∧
  Leaf146 f ∧
  Leaf147 f ∧
  Leaf148 f ∧
  Leaf149 f ∧
  Leaf150 f ∧
  Leaf151 f ∧
  Leaf152 f ∧
  Leaf153 f ∧
  Leaf154 f ∧
  Leaf155 f ∧
  Leaf156 f ∧
  Leaf157 f ∧
  Leaf158 f ∧
  Leaf159 f

def Group10 (f : Decide) : Prop :=
  Leaf160 f ∧
  Leaf161 f ∧
  Leaf162 f ∧
  Leaf163 f ∧
  Leaf164 f ∧
  Leaf165 f ∧
  Leaf166 f ∧
  Leaf167 f ∧
  Leaf168 f ∧
  Leaf169 f ∧
  Leaf170 f ∧
  Leaf171 f ∧
  Leaf172 f ∧
  Leaf173 f ∧
  Leaf174 f ∧
  Leaf175 f

def Group11 (f : Decide) : Prop :=
  Leaf176 f ∧
  Leaf177 f ∧
  Leaf178 f ∧
  Leaf179 f ∧
  Leaf180 f ∧
  Leaf181 f ∧
  Leaf182 f ∧
  Leaf183 f ∧
  Leaf184 f ∧
  Leaf185 f ∧
  Leaf186 f ∧
  Leaf187 f ∧
  Leaf188 f ∧
  Leaf189 f ∧
  Leaf190 f ∧
  Leaf191 f

def Group12 (f : Decide) : Prop :=
  Leaf192 f ∧
  Leaf193 f ∧
  Leaf194 f ∧
  Leaf195 f ∧
  Leaf196 f ∧
  Leaf197 f ∧
  Leaf198 f ∧
  Leaf199 f ∧
  Leaf200 f ∧
  Leaf201 f ∧
  Leaf202 f ∧
  Leaf203 f ∧
  Leaf204 f ∧
  Leaf205 f ∧
  Leaf206 f ∧
  Leaf207 f

def Group13 (f : Decide) : Prop :=
  Leaf208 f ∧
  Leaf209 f ∧
  Leaf210 f ∧
  Leaf211 f ∧
  Leaf212 f ∧
  Leaf213 f ∧
  Leaf214 f ∧
  Leaf215 f ∧
  Leaf216 f ∧
  Leaf217 f ∧
  Leaf218 f ∧
  Leaf219 f ∧
  Leaf220 f ∧
  Leaf221 f ∧
  Leaf222 f ∧
  Leaf223 f

def Group14 (f : Decide) : Prop :=
  Leaf224 f ∧
  Leaf225 f ∧
  Leaf226 f ∧
  Leaf227 f ∧
  Leaf228 f ∧
  Leaf229 f ∧
  Leaf230 f ∧
  Leaf231 f ∧
  Leaf232 f ∧
  Leaf233 f ∧
  Leaf234 f ∧
  Leaf235 f ∧
  Leaf236 f ∧
  Leaf237 f ∧
  Leaf238 f ∧
  Leaf239 f

def Group15 (f : Decide) : Prop :=
  Leaf240 f ∧
  Leaf241 f ∧
  Leaf242 f ∧
  Leaf243 f ∧
  Leaf244 f ∧
  Leaf245 f ∧
  Leaf246 f ∧
  Leaf247 f ∧
  Leaf248 f ∧
  Leaf249 f ∧
  Leaf250 f ∧
  Leaf251 f ∧
  Leaf252 f ∧
  Leaf253 f ∧
  Leaf254 f ∧
  Leaf255 f

def Group16 (f : Decide) : Prop :=
  Leaf256 f ∧
  Leaf257 f ∧
  Leaf258 f ∧
  Leaf259 f ∧
  Leaf260 f ∧
  Leaf261 f ∧
  Leaf262 f ∧
  Leaf263 f ∧
  Leaf264 f ∧
  Leaf265 f ∧
  Leaf266 f ∧
  Leaf267 f ∧
  Leaf268 f ∧
  Leaf269 f ∧
  Leaf270 f ∧
  Leaf271 f

def Group17 (f : Decide) : Prop :=
  Leaf272 f ∧
  Leaf273 f ∧
  Leaf274 f ∧
  Leaf275 f ∧
  Leaf276 f ∧
  Leaf277 f ∧
  Leaf278 f ∧
  Leaf279 f ∧
  Leaf280 f ∧
  Leaf281 f ∧
  Leaf282 f ∧
  Leaf283 f ∧
  Leaf284 f ∧
  Leaf285 f ∧
  Leaf286 f ∧
  Leaf287 f

def Group18 (f : Decide) : Prop :=
  Leaf288 f ∧
  Leaf289 f ∧
  Leaf290 f ∧
  Leaf291 f ∧
  Leaf292 f ∧
  Leaf293 f ∧
  Leaf294 f ∧
  Leaf295 f ∧
  Leaf296 f ∧
  Leaf297 f ∧
  Leaf298 f ∧
  Leaf299 f ∧
  Leaf300 f ∧
  Leaf301 f ∧
  Leaf302 f ∧
  Leaf303 f

def Group19 (f : Decide) : Prop :=
  Leaf304 f ∧
  Leaf305 f ∧
  Leaf306 f ∧
  Leaf307 f ∧
  Leaf308 f ∧
  Leaf309 f ∧
  Leaf310 f ∧
  Leaf311 f ∧
  Leaf312 f ∧
  Leaf313 f ∧
  Leaf314 f ∧
  Leaf315 f ∧
  Leaf316 f ∧
  Leaf317 f ∧
  Leaf318 f ∧
  Leaf319 f

def Group20 (f : Decide) : Prop :=
  Leaf320 f ∧
  Leaf321 f ∧
  Leaf322 f ∧
  Leaf323 f ∧
  Leaf324 f ∧
  Leaf325 f ∧
  Leaf326 f ∧
  Leaf327 f ∧
  Leaf328 f ∧
  Leaf329 f ∧
  Leaf330 f ∧
  Leaf331 f ∧
  Leaf332 f ∧
  Leaf333 f ∧
  Leaf334 f ∧
  Leaf335 f

def Group21 (f : Decide) : Prop :=
  Leaf336 f ∧
  Leaf337 f ∧
  Leaf338 f ∧
  Leaf339 f ∧
  Leaf340 f ∧
  Leaf341 f ∧
  Leaf342 f ∧
  Leaf343 f ∧
  Leaf344 f ∧
  Leaf345 f ∧
  Leaf346 f ∧
  Leaf347 f ∧
  Leaf348 f ∧
  Leaf350 f ∧
  Leaf351 f ∧
  Leaf352 f

def Group22 (f : Decide) : Prop :=
  Leaf353 f ∧
  Leaf354 f ∧
  Leaf355 f ∧
  Leaf356 f ∧
  Leaf357 f ∧
  Leaf358 f ∧
  Leaf359 f ∧
  Leaf360 f ∧
  Leaf361 f ∧
  Leaf362 f ∧
  Leaf363 f ∧
  Leaf364 f ∧
  Leaf365 f ∧
  Leaf366 f ∧
  Leaf367 f ∧
  Leaf368 f

def Group23 (f : Decide) : Prop :=
  Leaf369 f ∧
  Leaf370 f ∧
  Leaf371 f ∧
  Leaf372 f ∧
  Leaf373 f ∧
  Leaf374 f ∧
  Leaf375 f ∧
  Leaf376 f ∧
  Leaf377 f ∧
  Leaf378 f ∧
  Leaf379 f ∧
  Leaf380 f ∧
  Leaf381 f ∧
  Leaf382 f ∧
  Leaf383 f ∧
  Leaf384 f

def Group24 (f : Decide) : Prop :=
  Leaf385 f ∧
  Leaf386 f ∧
  Leaf387 f ∧
  Leaf388 f ∧
  Leaf389 f ∧
  Leaf390 f ∧
  Leaf391 f ∧
  Leaf392 f ∧
  Leaf393 f ∧
  Leaf394 f ∧
  Leaf395 f ∧
  Leaf396 f ∧
  Leaf397 f ∧
  Leaf398 f ∧
  Leaf399 f ∧
  Leaf400 f

def Group25 (f : Decide) : Prop :=
  Leaf401 f ∧
  Leaf402 f ∧
  Leaf403 f ∧
  Leaf404 f ∧
  Leaf405 f ∧
  Leaf406 f ∧
  Leaf407 f ∧
  Leaf408 f ∧
  Leaf409 f ∧
  Leaf410 f ∧
  Leaf411 f ∧
  Leaf412 f ∧
  Leaf413 f ∧
  Leaf414 f ∧
  Leaf415 f ∧
  Leaf416 f

def Group26 (f : Decide) : Prop :=
  Leaf417 f ∧
  Leaf418 f ∧
  Leaf419 f ∧
  Leaf420 f ∧
  Leaf421 f ∧
  Leaf422 f ∧
  Leaf423 f ∧
  Leaf424 f ∧
  Leaf425 f ∧
  Leaf426 f ∧
  Leaf427 f ∧
  Leaf428 f ∧
  Leaf429 f ∧
  Leaf430 f ∧
  Leaf431 f ∧
  Leaf432 f

def Group27 (f : Decide) : Prop :=
  Leaf433 f ∧
  Leaf434 f ∧
  Leaf435 f ∧
  Leaf436 f ∧
  Leaf437 f ∧
  Leaf438 f ∧
  Leaf439 f ∧
  Leaf440 f ∧
  Leaf441 f ∧
  Leaf442 f ∧
  Leaf443 f ∧
  Leaf444 f ∧
  Leaf445 f ∧
  Leaf446 f ∧
  Leaf447 f ∧
  Leaf448 f

def Group28 (f : Decide) : Prop :=
  Leaf449 f ∧
  Leaf450 f ∧
  Leaf451 f ∧
  Leaf452 f ∧
  Leaf453 f ∧
  Leaf454 f ∧
  Leaf455 f ∧
  Leaf456 f ∧
  Leaf457 f ∧
  Leaf458 f ∧
  Leaf459 f ∧
  Leaf460 f ∧
  Leaf461 f ∧
  Leaf462 f ∧
  Leaf463 f ∧
  Leaf464 f

def Group29 (f : Decide) : Prop :=
  Leaf465 f ∧
  Leaf466 f ∧
  Leaf467 f ∧
  Leaf468 f ∧
  Leaf469 f ∧
  Leaf470 f ∧
  Leaf471 f ∧
  Leaf472 f ∧
  Leaf473 f ∧
  Leaf474 f ∧
  Leaf475 f ∧
  Leaf476 f ∧
  Leaf477 f ∧
  Leaf478 f ∧
  Leaf479 f ∧
  Leaf480 f

def Group30 (f : Decide) : Prop :=
  Leaf481 f ∧
  Leaf482 f ∧
  Leaf483 f ∧
  Leaf484 f ∧
  Leaf485 f ∧
  Leaf486 f ∧
  Leaf487 f ∧
  Leaf488 f ∧
  Leaf489 f ∧
  Leaf490 f ∧
  Leaf491 f ∧
  Leaf492 f ∧
  Leaf493 f ∧
  Leaf494 f ∧
  Leaf495 f ∧
  Leaf496 f

def Group31 (f : Decide) : Prop :=
  Leaf497 f ∧
  Leaf498 f ∧
  Leaf499 f ∧
  Leaf500 f ∧
  Leaf501 f ∧
  Leaf502 f ∧
  Leaf503 f ∧
  Leaf504 f ∧
  Leaf505 f ∧
  Leaf506 f ∧
  Leaf507 f ∧
  Leaf508 f ∧
  Leaf509 f ∧
  Leaf510 f ∧
  Leaf511 f

/-- A rule passes when each law holds for it. -/
def Passes (f : Decide) : Prop :=
  Group0 f ∧
  Group1 f ∧
  Group2 f ∧
  Group3 f ∧
  Group4 f ∧
  Group5 f ∧
  Group6 f ∧
  Group7 f ∧
  Group8 f ∧
  Group9 f ∧
  Group10 f ∧
  Group11 f ∧
  Group12 f ∧
  Group13 f ∧
  Group14 f ∧
  Group15 f ∧
  Group16 f ∧
  Group17 f ∧
  Group18 f ∧
  Group19 f ∧
  Group20 f ∧
  Group21 f ∧
  Group22 f ∧
  Group23 f ∧
  Group24 f ∧
  Group25 f ∧
  Group26 f ∧
  Group27 f ∧
  Group28 f ∧
  Group29 f ∧
  Group30 f ∧
  Group31 f

end Tbl
