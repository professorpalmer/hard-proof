/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Leaf0 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = false → c.b9 = false → f c = false
def Leaf1 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = false → c.b9 = true → f c = true
def Leaf2 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = true → c.b8 = false → c.b1 = false → f c = true
def Leaf3 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = true → c.b8 = false → c.b1 = true → f c = false
def Leaf4 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = true → c.b8 = true → c.b9 = false → c.b0 = false → c.b12 = false → c.b10 = false → f c = false
def Leaf5 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = true → c.b8 = true → c.b9 = false → c.b0 = false → c.b12 = false → c.b10 = true → f c = false
def Leaf6 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = true → c.b8 = true → c.b9 = false → c.b0 = false → c.b12 = true → f c = true
def Leaf7 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = true → c.b8 = true → c.b9 = false → c.b0 = true → f c = true
def Leaf8 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b5 = true → c.b8 = true → c.b9 = true → f c = true
def Leaf9 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = false → c.b4 = false → c.b6 = false → f c = false
def Leaf10 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = false → c.b4 = false → c.b6 = true → c.b10 = false → f c = false
def Leaf11 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = false → c.b4 = false → c.b6 = true → c.b10 = true → f c = true
def Leaf12 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = false → c.b4 = true → c.b12 = false → f c = false
def Leaf13 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = false → c.b4 = true → c.b12 = true → f c = true
def Leaf14 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = true → c.b12 = false → c.b3 = false → f c = false
def Leaf15 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = true → c.b12 = false → c.b3 = true → f c = false
def Leaf16 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = false → c.b8 = true → c.b12 = true → f c = false
def Leaf17 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = false → c.b7 = true → f c = false
def Leaf18 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = true → c.b10 = false → c.b6 = false → f c = true
def Leaf19 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = true → c.b10 = false → c.b6 = true → f c = false
def Leaf20 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = true → c.b10 = true → c.b7 = false → c.b9 = false → f c = false
def Leaf21 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = true → c.b10 = true → c.b7 = false → c.b9 = true → f c = true
def Leaf22 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = false → c.b1 = true → c.b10 = true → c.b7 = true → f c = false
def Leaf23 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = false → c.b4 = false → c.b8 = false → c.b1 = false → f c = true
def Leaf24 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = false → c.b4 = false → c.b8 = false → c.b1 = true → f c = false
def Leaf25 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = false → c.b4 = false → c.b8 = true → f c = false
def Leaf26 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = false → c.b4 = true → c.b8 = false → c.b6 = false → f c = true
def Leaf27 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = false → c.b4 = true → c.b8 = false → c.b6 = true → f c = true
def Leaf28 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = false → c.b4 = true → c.b8 = true → c.b1 = false → f c = true
def Leaf29 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = false → c.b4 = true → c.b8 = true → c.b1 = true → f c = false
def Leaf30 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = true → c.b10 = false → c.b3 = false → f c = false
def Leaf31 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = true → c.b10 = false → c.b3 = true → c.b1 = false → f c = false
def Leaf32 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = true → c.b10 = false → c.b3 = true → c.b1 = true → f c = false
def Leaf33 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = false → c.b5 = true → c.b9 = true → c.b10 = true → f c = false
def Leaf34 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b12 = false → c.b8 = false → c.b4 = false → f c = false
def Leaf35 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b12 = false → c.b8 = false → c.b4 = true → f c = false
def Leaf36 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b12 = false → c.b8 = true → f c = false
def Leaf37 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b12 = true → c.b9 = false → c.b7 = false → f c = false
def Leaf38 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b12 = true → c.b9 = false → c.b7 = true → c.b8 = false → f c = true
def Leaf39 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b12 = true → c.b9 = false → c.b7 = true → c.b8 = true → f c = false
def Leaf40 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b12 = true → c.b9 = true → f c = true
def Leaf41 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = true → c.b8 = false → f c = false
def Leaf42 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = true → c.b8 = true → c.b10 = false → f c = true
def Leaf43 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = false → c.b0 = true → c.b5 = true → c.b8 = true → c.b10 = true → f c = true
def Leaf44 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = false → f c = false
def Leaf45 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = false → c.b1 = false → c.b5 = false → f c = false
def Leaf46 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = false → c.b1 = false → c.b5 = true → f c = false
def Leaf47 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = false → c.b1 = true → f c = true
def Leaf48 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = true → c.b1 = false → c.b5 = false → c.b8 = false → f c = true
def Leaf49 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = true → c.b1 = false → c.b5 = false → c.b8 = true → f c = false
def Leaf50 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = true → c.b1 = false → c.b5 = true → c.b8 = false → f c = true
def Leaf51 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = true → c.b1 = false → c.b5 = true → c.b8 = true → f c = true
def Leaf52 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = true → c.b1 = true → c.b5 = false → f c = true
def Leaf53 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = false → c.b10 = true → c.b1 = true → c.b5 = true → f c = false
def Leaf54 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = true → c.b8 = false → f c = false
def Leaf55 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = false → c.b4 = true → c.b8 = true → f c = true
def Leaf56 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = true → c.b10 = false → f c = true
def Leaf57 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = false → c.b3 = true → c.b10 = true → f c = true
def Leaf58 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = true → c.b1 = false → f c = true
def Leaf59 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = false → c.b0 = true → c.b1 = true → f c = true
def Leaf60 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = false → c.b0 = false → c.b10 = false → f c = false
def Leaf61 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = false → c.b0 = false → c.b10 = true → c.b8 = false → f c = false
def Leaf62 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = false → c.b0 = false → c.b10 = true → c.b8 = true → f c = true
def Leaf63 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = false → c.b0 = true → c.b1 = false → f c = true
def Leaf64 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = false → c.b0 = true → c.b1 = true → f c = true
def Leaf65 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = true → c.b1 = false → c.b10 = false → c.b8 = false → f c = false
def Leaf66 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = true → c.b1 = false → c.b10 = false → c.b8 = true → c.b9 = false → f c = true
def Leaf67 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = true → c.b1 = false → c.b10 = false → c.b8 = true → c.b9 = true → f c = false
def Leaf68 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = true → c.b1 = false → c.b10 = true → f c = true
def Leaf69 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = true → c.b1 = true → c.b9 = false → f c = false
def Leaf70 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = false → c.b7 = true → c.b4 = true → c.b1 = true → c.b9 = true → f c = false
def Leaf71 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = true → c.b8 = false → f c = true
def Leaf72 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b11 = true → c.b6 = true → c.b12 = true → c.b8 = true → f c = true
def Leaf73 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = false → c.b6 = false → f c = false
def Leaf74 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = false → c.b6 = true → c.b7 = false → c.b3 = false → f c = true
def Leaf75 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = false → c.b6 = true → c.b7 = false → c.b3 = true → f c = true
def Leaf76 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = false → c.b6 = true → c.b7 = true → f c = true
def Leaf77 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = false → f c = true
def Leaf78 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = false → c.b3 = false → f c = false
def Leaf79 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = false → c.b3 = true → f c = false
def Leaf80 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = false → c.b7 = false → f c = true
def Leaf81 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = false → c.b7 = true → f c = false
def Leaf82 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = true → c.b5 = false → c.b10 = false → f c = true
def Leaf83 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = true → c.b5 = false → c.b10 = true → c.b12 = false → c.b1 = false → f c = true
def Leaf84 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = true → c.b5 = false → c.b10 = true → c.b12 = false → c.b1 = true → f c = false
def Leaf85 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = true → c.b5 = false → c.b10 = true → c.b12 = true → c.b7 = false → f c = false
def Leaf86 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = true → c.b5 = false → c.b10 = true → c.b12 = true → c.b7 = true → f c = true
def Leaf87 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = false → c.b13 = true → c.b9 = true → c.b8 = true → c.b5 = true → f c = true
def Leaf88 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = false → c.b1 = false → f c = false
def Leaf89 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = false → c.b1 = true → f c = true
def Leaf90 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = true → c.b5 = false → c.b7 = false → f c = true
def Leaf91 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = true → c.b5 = false → c.b7 = true → f c = true
def Leaf92 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = true → c.b5 = true → c.b8 = false → c.b7 = false → f c = true
def Leaf93 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = true → c.b5 = true → c.b8 = false → c.b7 = true → f c = true
def Leaf94 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = true → c.b5 = true → c.b8 = true → c.b13 = false → f c = false
def Leaf95 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = false → c.b12 = true → c.b5 = true → c.b8 = true → c.b13 = true → f c = false
def Leaf96 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = true → c.b8 = false → f c = false
def Leaf97 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = true → c.b8 = true → c.b1 = false → f c = true
def Leaf98 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = false → c.b9 = true → c.b8 = true → c.b1 = true → f c = true
def Leaf99 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = true → c.b8 = false → f c = false
def Leaf100 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = false → c.b10 = true → c.b8 = true → f c = false
def Leaf101 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = false → c.b1 = false → c.b12 = false → c.b5 = false → c.b9 = false → f c = false
def Leaf102 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = false → c.b1 = false → c.b12 = false → c.b5 = false → c.b9 = true → c.b10 = false → f c = false
def Leaf103 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = false → c.b1 = false → c.b12 = false → c.b5 = false → c.b9 = true → c.b10 = true → f c = false
def Leaf104 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = false → c.b1 = false → c.b12 = false → c.b5 = true → f c = false
def Leaf105 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = false → c.b1 = false → c.b12 = true → f c = true
def Leaf106 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = false → c.b1 = true → f c = true
def Leaf107 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = true → c.b13 = false → f c = false
def Leaf108 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = true → c.b13 = true → c.b1 = false → c.b5 = false → f c = true
def Leaf109 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = true → c.b13 = true → c.b1 = false → c.b5 = true → c.b8 = false → f c = true
def Leaf110 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = true → c.b13 = true → c.b1 = false → c.b5 = true → c.b8 = true → c.b12 = false → c.b9 = false → f c = true
def Leaf111 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = true → c.b13 = true → c.b1 = false → c.b5 = true → c.b8 = true → c.b12 = false → c.b9 = true → f c = true
def Leaf112 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = true → c.b13 = true → c.b1 = false → c.b5 = true → c.b8 = true → c.b12 = true → f c = true
def Leaf113 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = false → c.b11 = true → c.b3 = true → c.b7 = true → c.b13 = true → c.b1 = true → f c = false
def Leaf114 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = false → c.b6 = true → f c = true
def Leaf115 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = false → c.b12 = false → c.b3 = false → f c = false
def Leaf116 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = false → c.b12 = false → c.b3 = true → c.b1 = false → f c = true
def Leaf117 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = false → c.b12 = false → c.b3 = true → c.b1 = true → f c = false
def Leaf118 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = false → c.b12 = true → c.b8 = false → f c = false
def Leaf119 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = false → c.b12 = true → c.b8 = true → f c = true
def Leaf120 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = true → c.b11 = false → c.b12 = false → f c = true
def Leaf121 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = true → c.b11 = false → c.b12 = true → f c = false
def Leaf122 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = true → c.b11 = true → c.b13 = false → f c = true
def Leaf123 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = false → c.b7 = true → c.b11 = true → c.b13 = true → f c = true
def Leaf124 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = true → c.b13 = false → c.b11 = false → c.b7 = false → f c = true
def Leaf125 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = true → c.b13 = false → c.b11 = false → c.b7 = true → f c = true
def Leaf126 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = true → c.b13 = false → c.b11 = true → f c = true
def Leaf127 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = true → c.b0 = true → c.b9 = true → c.b13 = true → f c = true

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
  Leaf25 f ∧
  Leaf26 f ∧
  Leaf27 f ∧
  Leaf28 f ∧
  Leaf29 f ∧
  Leaf30 f ∧
  Leaf31 f ∧
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
  Leaf47 f ∧
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
  Leaf63 f ∧
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
  Leaf79 f ∧
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
  Leaf95 f ∧
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
  Leaf111 f ∧
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

end Tbl
