/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Law0 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b11 = false → c.b13 = false → c.b9 = false → c.b3 = true → c.b8 = false → c.b12 = true → c.b10 = false → c.b15 = true → c.b0 = false → c.b14 = false → c.b6 = true → f c = false
def Law1 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b9 = true → c.b4 = true → c.b16 = true → c.b12 = true → c.b1 = false → c.b7 = false → c.b3 = false → f c = false
def Law2 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b0 = false → c.b3 = false → c.b1 = true → c.b14 = true → c.b6 = false → c.b17 = true → c.b15 = true → c.b5 = false → c.b13 = false → c.b7 = false → c.b8 = false → c.b12 = true → c.b10 = true → f c = false
def Law3 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b8 = true → c.b9 = true → c.b2 = false → c.b6 = false → c.b13 = false → c.b17 = false → c.b14 = false → c.b1 = true → c.b16 = false → c.b11 = false → c.b7 = true → c.b0 = false → c.b12 = true → c.b15 = true → f c = false
def Law4 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b5 = false → c.b4 = true → c.b1 = true → c.b14 = false → c.b10 = false → c.b13 = false → c.b0 = false → c.b7 = true → c.b2 = true → c.b17 = false → c.b16 = true → c.b8 = false → c.b6 = true → c.b3 = false → c.b12 = true → c.b15 = true → f c = false
def Law5 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b8 = false → c.b0 = true → c.b14 = false → c.b12 = true → c.b1 = true → c.b2 = false → c.b9 = true → c.b3 = false → c.b7 = false → c.b6 = true → c.b4 = false → f c = true
def Law6 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b10 = true → c.b0 = true → c.b6 = false → c.b12 = false → c.b8 = false → c.b1 = true → c.b7 = false → f c = true
def Law7 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b6 = true → c.b1 = true → c.b11 = false → c.b14 = false → c.b5 = true → c.b8 = true → c.b0 = true → c.b16 = false → c.b7 = false → c.b9 = true → c.b10 = true → c.b15 = false → f c = true
def Law8 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b10 = false → c.b6 = true → c.b12 = false → c.b0 = false → c.b7 = true → c.b14 = true → c.b15 = false → c.b1 = true → f c = false
def Law9 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b5 = false → c.b1 = true → c.b6 = false → c.b8 = false → c.b7 = true → c.b16 = true → c.b4 = false → c.b13 = true → c.b14 = false → c.b10 = true → c.b11 = false → c.b15 = true → c.b0 = true → f c = false
def Law10 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b16 = true → c.b13 = true → c.b7 = false → c.b14 = true → c.b4 = false → c.b6 = false → c.b1 = true → c.b10 = false → c.b9 = false → c.b0 = true → f c = false
def Law11 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b0 = false → c.b12 = true → c.b3 = false → c.b4 = true → c.b17 = false → c.b16 = true → c.b6 = false → c.b10 = true → c.b5 = false → c.b1 = true → c.b7 = true → c.b13 = false → c.b9 = true → f c = true
def Law12 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b7 = true → c.b12 = true → c.b1 = true → c.b10 = false → c.b0 = false → c.b6 = false → c.b2 = true → c.b14 = false → c.b15 = true → c.b5 = false → c.b4 = false → c.b17 = true → f c = false
def Law13 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b9 = true → c.b10 = true → c.b11 = false → c.b12 = false → c.b14 = false → c.b0 = true → c.b4 = false → c.b5 = true → c.b1 = true → c.b6 = false → c.b3 = true → c.b16 = true → c.b15 = true → c.b8 = false → f c = false
def Law14 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b7 = true → c.b11 = false → c.b10 = true → c.b16 = false → c.b1 = true → c.b5 = true → c.b14 = false → c.b15 = true → c.b0 = true → c.b4 = false → c.b3 = true → c.b8 = false → c.b12 = false → c.b6 = false → f c = false
def Law15 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b9 = false → c.b16 = true → c.b6 = true → c.b17 = false → c.b11 = false → c.b1 = true → c.b0 = true → c.b10 = true → f c = false
def Law16 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b6 = true → c.b8 = false → c.b2 = true → c.b7 = false → c.b14 = false → c.b0 = true → c.b9 = true → c.b10 = true → c.b1 = true → f c = true
def Law17 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b2 = true → c.b16 = false → c.b0 = true → c.b12 = false → c.b8 = true → c.b3 = true → c.b11 = true → c.b14 = false → c.b4 = false → c.b1 = true → c.b10 = true → c.b7 = true → c.b6 = true → c.b5 = false → c.b9 = true → f c = false
def Law18 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b8 = true → c.b16 = false → c.b14 = false → c.b4 = true → c.b1 = true → c.b6 = false → c.b7 = false → c.b10 = false → f c = true
def Law19 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b3 = false → c.b12 = true → c.b17 = false → c.b11 = false → c.b1 = true → c.b14 = true → c.b9 = false → c.b8 = true → c.b7 = true → c.b10 = true → c.b16 = false → c.b0 = false → f c = false
def Law20 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b17 = false → c.b1 = true → c.b13 = false → c.b10 = false → c.b9 = false → c.b0 = false → c.b2 = false → c.b6 = false → c.b15 = true → c.b11 = false → c.b12 = true → c.b7 = true → f c = false
def Law21 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b11 = true → c.b10 = true → c.b8 = true → c.b7 = true → c.b0 = true → c.b12 = true → c.b4 = true → c.b14 = false → c.b9 = true → c.b6 = true → c.b13 = true → f c = false
def Law22 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b4 = false → c.b7 = false → c.b2 = true → c.b13 = false → c.b0 = false → c.b1 = true → c.b17 = false → c.b15 = true → c.b10 = true → c.b16 = true → c.b12 = true → c.b14 = false → c.b8 = true → f c = false
def Law23 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b5 = true → c.b12 = true → c.b1 = true → c.b7 = true → c.b14 = false → c.b17 = true → c.b6 = false → c.b10 = false → c.b3 = false → c.b0 = false → f c = false
def Law24 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b0 = true → c.b12 = true → c.b1 = true → c.b13 = true → c.b17 = true → c.b10 = true → c.b7 = false → c.b6 = true → c.b9 = true → c.b11 = true → c.b14 = false → c.b5 = true → c.b16 = false → f c = false
def Law25 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b0 = false → c.b14 = false → c.b13 = true → c.b6 = false → c.b11 = false → c.b12 = true → c.b8 = true → c.b9 = true → c.b7 = false → c.b3 = true → c.b10 = true → c.b16 = true → c.b1 = true → c.b17 = true → f c = true
def Law26 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b8 = false → c.b3 = false → c.b4 = false → c.b0 = true → c.b6 = false → c.b16 = true → c.b10 = false → c.b1 = true → c.b9 = false → c.b2 = false → c.b11 = true → c.b14 = false → f c = true
def Law27 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b1 = true → c.b6 = false → c.b4 = false → c.b3 = true → c.b10 = true → c.b17 = false → c.b7 = true → f c = false
def Law28 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b10 = false → c.b13 = false → c.b5 = false → c.b17 = true → c.b6 = false → c.b16 = true → c.b12 = true → c.b15 = true → c.b14 = true → c.b1 = true → c.b2 = true → c.b4 = true → c.b7 = true → f c = true
def Law29 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b16 = false → c.b0 = false → c.b1 = true → c.b12 = false → c.b4 = true → c.b6 = false → f c = true
def Law30 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b0 = false → c.b10 = false → c.b9 = true → c.b8 = false → c.b5 = false → c.b7 = false → c.b12 = false → c.b1 = true → c.b6 = true → c.b17 = true → c.b14 = true → c.b16 = true → c.b15 = true → f c = false
def Law31 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b12 = true → c.b0 = false → c.b16 = false → c.b14 = false → c.b8 = false → c.b15 = true → c.b10 = false → c.b9 = true → c.b3 = false → c.b4 = true → c.b6 = true → c.b5 = false → f c = false
def Law32 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b1 = true → c.b10 = true → c.b0 = true → c.b17 = false → c.b7 = true → c.b8 = false → c.b16 = true → c.b2 = true → c.b14 = false → c.b9 = true → c.b5 = false → f c = true
def Law33 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b12 = true → c.b1 = true → c.b3 = true → c.b15 = true → c.b11 = false → c.b6 = true → c.b7 = true → c.b16 = true → c.b4 = true → c.b8 = false → c.b9 = true → c.b10 = false → c.b5 = false → c.b0 = false → f c = false
def Law34 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b4 = false → c.b11 = true → c.b12 = false → c.b2 = false → c.b1 = true → c.b13 = true → c.b7 = true → c.b10 = true → c.b14 = false → c.b16 = false → c.b6 = true → c.b0 = true → c.b8 = true → c.b9 = true → f c = false
def Law35 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b7 = true → c.b3 = false → c.b4 = false → c.b15 = true → c.b10 = true → c.b0 = true → c.b6 = false → c.b14 = false → c.b5 = true → c.b1 = true → c.b11 = false → c.b8 = false → f c = false
def Law36 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b11 = false → c.b0 = false → c.b6 = false → c.b16 = false → c.b14 = true → c.b12 = false → c.b4 = true → f c = true
def Law37 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b1 = true → c.b7 = true → c.b0 = true → c.b14 = true → c.b15 = true → c.b4 = true → f c = false
def Law38 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b1 = true → c.b17 = false → c.b15 = true → c.b6 = true → c.b2 = false → c.b12 = false → c.b10 = false → c.b13 = false → f c = true
def Law39 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b10 = true → c.b1 = true → c.b16 = false → c.b0 = true → c.b11 = true → c.b14 = false → c.b6 = true → c.b9 = false → f c = false
def Law40 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b9 = true → c.b12 = true → c.b10 = true → c.b7 = true → c.b16 = false → c.b0 = false → c.b8 = false → c.b3 = false → c.b15 = false → c.b13 = true → c.b17 = false → c.b6 = false → c.b11 = false → f c = true
def Law41 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b14 = false → c.b6 = true → c.b16 = false → c.b11 = true → c.b0 = false → c.b4 = true → c.b10 = false → c.b9 = true → c.b1 = true → c.b2 = false → c.b12 = true → c.b8 = false → c.b7 = true → f c = true
def Law42 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b7 = false → c.b1 = false → c.b16 = true → c.b6 = false → c.b4 = false → c.b12 = true → c.b3 = false → c.b15 = false → f c = false
def Law43 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b3 = false → c.b0 = false → c.b1 = true → c.b14 = true → c.b17 = false → c.b13 = true → c.b7 = true → c.b9 = false → c.b12 = true → c.b15 = false → c.b2 = false → c.b16 = false → c.b6 = false → c.b10 = true → f c = true
def Law44 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b5 = false → c.b10 = true → c.b7 = false → c.b0 = true → c.b11 = false → c.b14 = false → c.b8 = true → c.b6 = true → c.b4 = false → c.b16 = false → c.b15 = false → c.b1 = true → f c = false
def Law45 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b7 = true → c.b8 = true → c.b3 = false → f c = true
def Law46 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b7 = false → c.b10 = false → c.b0 = true → c.b9 = false → c.b16 = true → c.b14 = true → c.b13 = false → c.b1 = true → c.b4 = false → f c = true
def Law47 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b14 = false → c.b0 = false → c.b10 = false → c.b8 = true → c.b9 = false → c.b1 = true → c.b15 = true → c.b6 = true → c.b16 = false → c.b12 = true → f c = true
def Law48 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b1 = true → c.b15 = false → c.b6 = false → c.b3 = false → c.b10 = false → c.b4 = true → c.b7 = true → c.b14 = false → c.b12 = false → f c = true
def Law49 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b4 = false → c.b1 = false → c.b13 = true → c.b3 = false → c.b5 = false → c.b7 = false → f c = false
def Law50 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b14 = false → c.b9 = false → c.b4 = true → c.b3 = true → c.b16 = false → c.b1 = false → c.b5 = false → f c = false
def Law51 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b1 = true → c.b16 = true → c.b12 = true → c.b6 = false → c.b4 = false → c.b7 = false → c.b14 = false → c.b8 = false → f c = true
def Law52 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b15 = true → c.b17 = true → c.b12 = true → c.b5 = false → c.b6 = false → c.b10 = true → c.b4 = true → c.b7 = true → c.b1 = true → c.b13 = true → f c = false
def Law53 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b11 = true → c.b1 = true → c.b9 = true → c.b13 = true → c.b0 = false → c.b8 = false → c.b10 = false → c.b2 = true → c.b15 = false → c.b16 = false → c.b6 = true → f c = true
def Law54 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b14 = false → c.b6 = false → c.b17 = false → c.b15 = true → c.b13 = true → c.b1 = true → c.b16 = false → c.b4 = true → c.b12 = true → c.b10 = true → c.b3 = false → c.b0 = false → c.b9 = false → c.b11 = true → f c = false
def Law55 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = true → c.b14 = true → c.b15 = false → c.b17 = true → c.b7 = false → c.b6 = false → c.b0 = false → c.b5 = false → c.b1 = true → c.b3 = false → c.b13 = false → c.b10 = true → c.b8 = false → f c = true
def Law56 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b4 = false → c.b8 = true → c.b12 = false → c.b13 = true → c.b16 = false → c.b2 = true → c.b6 = true → c.b5 = true → c.b3 = true → c.b10 = true → c.b7 = true → c.b11 = true → c.b1 = true → c.b0 = true → c.b9 = true → f c = false
def Law57 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b7 = true → c.b16 = false → c.b17 = false → c.b3 = false → c.b11 = false → c.b12 = true → c.b0 = false → c.b8 = false → c.b1 = true → c.b9 = false → c.b6 = false → f c = false
def Law58 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b10 = false → c.b7 = false → c.b15 = true → c.b16 = true → c.b8 = false → c.b13 = false → c.b4 = true → c.b14 = false → c.b0 = false → c.b6 = true → c.b3 = false → c.b12 = true → c.b5 = false → c.b9 = true → c.b11 = true → f c = false
def Law59 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b17 = true → c.b1 = true → c.b0 = false → c.b10 = false → c.b6 = true → c.b16 = false → c.b2 = false → c.b4 = true → c.b12 = false → f c = true
def Law60 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b14 = false → c.b10 = true → c.b1 = true → c.b9 = true → c.b6 = true → c.b0 = true → c.b8 = false → c.b5 = false → c.b2 = true → f c = false
def Law61 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b15 = true → c.b6 = false → c.b7 = false → c.b16 = true → c.b14 = false → c.b4 = false → c.b12 = true → c.b0 = false → c.b17 = false → c.b2 = true → c.b13 = true → c.b1 = true → f c = true
def Law62 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b10 = false → c.b5 = true → c.b6 = true → c.b16 = true → c.b17 = true → c.b12 = false → c.b9 = true → c.b14 = true → c.b4 = false → c.b11 = true → c.b0 = false → f c = true
def Law63 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b1 = false → c.b5 = true → c.b7 = true → c.b14 = false → c.b9 = false → c.b11 = false → c.b3 = true → c.b13 = false → f c = true
def Law64 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b7 = false → c.b0 = false → c.b4 = true → c.b12 = true → c.b1 = true → c.b17 = true → c.b8 = true → c.b10 = true → c.b6 = false → c.b5 = true → f c = false
def Law65 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b6 = true → c.b2 = false → c.b11 = false → c.b1 = true → c.b12 = false → c.b14 = true → c.b16 = true → c.b10 = false → c.b0 = false → c.b4 = true → c.b3 = false → f c = false
def Law66 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b0 = true → c.b14 = false → c.b7 = true → c.b3 = true → c.b5 = false → c.b6 = false → c.b1 = true → f c = false
def Law67 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b12 = true → c.b1 = false → c.b16 = true → c.b7 = false → c.b4 = true → c.b3 = false → c.b11 = true → f c = true
def Law68 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b11 = false → c.b1 = true → c.b8 = false → c.b6 = false → c.b10 = false → c.b17 = false → c.b7 = true → c.b9 = false → c.b16 = false → c.b15 = false → c.b13 = false → c.b2 = false → c.b5 = false → f c = false
def Law69 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b8 = true → c.b4 = false → c.b10 = true → c.b1 = true → c.b6 = true → c.b14 = false → c.b12 = false → c.b11 = true → c.b9 = true → c.b13 = true → c.b3 = false → c.b7 = true → f c = false
def Law70 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b15 = true → c.b9 = true → c.b8 = false → c.b7 = true → c.b17 = true → c.b4 = false → c.b1 = true → c.b5 = false → c.b6 = true → c.b16 = true → c.b10 = false → c.b0 = false → c.b14 = true → f c = false
def Law71 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b10 = true → c.b6 = true → c.b7 = false → c.b0 = false → c.b4 = true → c.b16 = true → f c = true
def Law72 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b0 = true → c.b7 = true → c.b4 = false → c.b15 = true → c.b6 = false → c.b1 = true → f c = true
def Law73 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b10 = true → c.b3 = false → c.b1 = true → c.b0 = true → c.b7 = false → c.b6 = true → c.b16 = true → c.b9 = false → c.b12 = true → c.b11 = true → f c = false
def Law74 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b12 = true → c.b7 = true → c.b1 = true → c.b10 = true → c.b16 = true → c.b14 = false → c.b3 = false → c.b9 = false → c.b11 = true → c.b6 = true → f c = false
def Law75 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b6 = true → c.b0 = false → c.b10 = false → c.b9 = false → c.b1 = true → c.b14 = true → c.b11 = false → f c = false
def Law76 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b15 = true → c.b4 = false → c.b9 = false → c.b1 = true → c.b6 = false → c.b7 = false → c.b0 = false → c.b12 = false → c.b17 = false → f c = true
def Law77 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b12 = true → c.b1 = true → c.b15 = false → c.b10 = false → c.b0 = false → c.b14 = false → c.b7 = false → c.b3 = false → c.b17 = true → c.b9 = false → c.b2 = false → c.b5 = false → c.b16 = true → c.b8 = true → f c = true
def Law78 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b16 = false → c.b7 = true → c.b10 = false → c.b11 = false → c.b17 = false → c.b13 = false → c.b12 = true → c.b2 = false → c.b9 = false → c.b1 = true → c.b0 = false → c.b6 = false → f c = true
def Law79 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b17 = true → c.b5 = true → c.b14 = true → c.b0 = false → c.b10 = false → c.b4 = false → c.b11 = false → c.b16 = true → c.b1 = true → c.b9 = true → c.b12 = false → f c = false
def Law80 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b11 = true → c.b13 = true → c.b10 = false → c.b6 = false → c.b8 = true → c.b7 = true → c.b1 = true → c.b16 = true → c.b3 = false → c.b14 = true → c.b17 = true → c.b2 = true → c.b12 = true → c.b0 = false → f c = false
def Law81 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b6 = true → c.b11 = true → c.b10 = false → c.b5 = false → c.b12 = true → c.b15 = true → c.b1 = true → c.b9 = true → c.b16 = true → c.b7 = true → c.b14 = false → c.b0 = false → c.b4 = true → c.b8 = false → f c = true
def Law82 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b16 = true → c.b8 = false → c.b3 = false → c.b11 = false → c.b1 = true → c.b10 = false → c.b2 = true → c.b15 = true → c.b0 = false → c.b12 = true → c.b7 = true → c.b6 = true → c.b14 = false → c.b5 = false → c.b4 = true → c.b9 = true → f c = false
def Law83 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b12 = false → c.b13 = false → c.b6 = true → c.b2 = true → c.b3 = false → c.b17 = false → c.b10 = false → c.b15 = true → c.b0 = false → c.b4 = false → f c = false
def Law84 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b17 = true → c.b13 = true → c.b2 = true → c.b1 = true → c.b6 = false → c.b12 = true → c.b3 = false → c.b16 = true → c.b0 = false → c.b7 = false → c.b14 = false → c.b11 = false → c.b8 = true → f c = true
def Law85 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b1 = true → c.b8 = false → c.b7 = false → c.b6 = false → c.b0 = false → c.b5 = true → c.b12 = true → c.b14 = true → c.b10 = true → f c = false
def Law86 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b10 = true → c.b0 = false → c.b15 = true → c.b12 = true → c.b8 = true → c.b17 = false → c.b7 = true → c.b3 = false → c.b5 = false → c.b16 = true → c.b6 = false → c.b11 = false → c.b9 = false → f c = true
def Law87 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b16 = false → c.b0 = false → c.b3 = false → c.b15 = true → c.b8 = true → c.b13 = false → c.b17 = false → c.b1 = true → c.b12 = true → c.b10 = false → c.b9 = true → c.b2 = false → c.b7 = true → c.b6 = false → c.b11 = false → f c = true
def Law88 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b1 = true → c.b4 = false → c.b3 = true → c.b0 = true → c.b16 = true → c.b6 = false → c.b14 = true → c.b9 = false → c.b13 = true → c.b7 = false → f c = false
def Law89 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b3 = false → c.b10 = true → c.b1 = true → c.b0 = false → c.b7 = true → c.b6 = true → f c = false
def Law90 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b0 = false → c.b7 = true → c.b12 = true → c.b9 = true → c.b17 = false → c.b11 = true → c.b5 = false → c.b1 = true → c.b3 = false → c.b10 = true → c.b4 = true → c.b16 = false → f c = true
def Law91 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b8 = true → c.b3 = false → c.b16 = true → c.b2 = false → c.b11 = true → c.b6 = false → c.b10 = false → c.b17 = false → c.b0 = false → c.b7 = true → c.b12 = true → f c = false
def Law92 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b0 = true → c.b10 = true → c.b2 = true → c.b6 = true → c.b1 = true → f c = true
def Law93 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b12 = true → c.b5 = false → c.b8 = true → c.b0 = false → c.b7 = true → c.b16 = true → c.b17 = true → c.b15 = true → c.b2 = false → c.b1 = true → c.b6 = false → f c = true
def Law94 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b11 = true → c.b14 = true → c.b5 = true → c.b3 = true → c.b16 = false → f c = true
def Law95 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b1 = true → c.b9 = false → c.b15 = false → c.b3 = false → c.b5 = true → c.b17 = true → c.b16 = true → c.b8 = true → c.b2 = false → c.b0 = false → c.b7 = false → c.b14 = false → c.b12 = true → f c = true
def Law96 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b2 = true → c.b10 = true → c.b7 = true → c.b12 = false → c.b13 = false → c.b3 = false → c.b4 = true → c.b14 = false → c.b1 = true → c.b6 = false → c.b0 = true → f c = false
def Law97 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b15 = false → c.b7 = true → c.b16 = false → c.b4 = true → c.b1 = true → c.b5 = false → c.b3 = false → c.b8 = false → c.b2 = false → c.b6 = false → c.b13 = false → c.b14 = false → c.b12 = true → f c = true
def Law98 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b14 = false → c.b17 = false → c.b0 = false → c.b3 = true → c.b6 = true → c.b2 = true → c.b1 = true → c.b12 = false → c.b10 = false → c.b15 = true → f c = true
def Law99 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b14 = false → c.b16 = false → c.b10 = true → c.b0 = true → c.b6 = true → c.b11 = false → c.b17 = false → c.b1 = true → f c = false
def Law100 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b17 = false → c.b11 = true → c.b9 = false → c.b16 = true → c.b0 = false → c.b3 = false → c.b10 = true → c.b7 = true → c.b12 = true → c.b15 = true → c.b8 = true → c.b5 = false → c.b6 = false → f c = true
def Law101 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b12 = false → c.b2 = true → c.b1 = true → c.b10 = false → c.b4 = true → c.b8 = true → c.b6 = true → c.b16 = true → c.b15 = true → c.b17 = false → c.b5 = true → c.b13 = true → c.b7 = false → c.b9 = true → f c = false
def Law102 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b10 = true → c.b13 = true → c.b16 = false → c.b0 = false → c.b12 = true → c.b17 = false → c.b5 = true → c.b6 = false → c.b8 = true → c.b9 = false → c.b14 = true → c.b1 = true → c.b7 = true → c.b15 = true → c.b11 = true → c.b4 = true → f c = false
def Law103 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b15 = true → c.b4 = false → c.b16 = true → c.b12 = false → c.b0 = false → c.b9 = true → c.b10 = false → c.b14 = false → c.b17 = true → c.b6 = true → c.b1 = true → f c = true
def Law104 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b13 = true → c.b2 = false → c.b10 = false → c.b12 = true → c.b1 = true → c.b11 = true → c.b0 = false → c.b6 = true → c.b7 = false → f c = true
def Law105 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b6 = false → c.b4 = false → c.b15 = false → c.b7 = false → c.b12 = false → c.b3 = false → c.b1 = false → c.b16 = true → f c = false
def Law106 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b13 = false → c.b12 = true → c.b6 = true → c.b10 = false → c.b0 = false → c.b11 = false → c.b9 = false → c.b8 = false → c.b3 = false → c.b14 = false → c.b15 = true → f c = true
def Law107 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b13 = false → c.b16 = true → c.b15 = true → c.b0 = false → c.b6 = false → c.b10 = true → c.b12 = true → c.b5 = false → c.b1 = true → c.b7 = true → f c = true
def Law108 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b1 = true → c.b2 = true → c.b6 = false → c.b0 = false → c.b11 = false → c.b17 = false → c.b7 = true → c.b12 = true → f c = true
def Law109 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b1 = false → c.b7 = false → c.b4 = true → c.b3 = false → c.b16 = true → c.b12 = false → f c = false
def Law110 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b2 = true → c.b16 = true → c.b8 = true → c.b4 = false → c.b5 = true → c.b7 = true → c.b0 = true → c.b1 = false → c.b11 = true → c.b3 = true → f c = true
def Law111 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b2 = false → c.b1 = true → c.b16 = true → c.b6 = false → c.b7 = false → c.b0 = true → c.b4 = false → c.b9 = true → f c = true
def Law112 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b0 = false → c.b12 = true → c.b15 = false → c.b1 = true → c.b5 = true → c.b16 = true → c.b7 = true → c.b13 = true → c.b14 = true → c.b8 = true → c.b6 = false → c.b17 = true → c.b3 = false → c.b2 = true → f c = true
def Law113 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b5 = true → c.b3 = true → c.b7 = true → c.b6 = false → c.b14 = false → c.b1 = true → c.b4 = true → f c = false
def Law114 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = true → c.b0 = false → c.b8 = true → c.b14 = false → c.b16 = true → c.b10 = false → c.b11 = false → c.b17 = false → c.b6 = false → c.b2 = false → c.b1 = true → c.b7 = false → f c = false
def Law115 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b11 = false → c.b0 = false → c.b13 = true → c.b9 = true → c.b12 = true → c.b16 = false → c.b15 = true → c.b8 = false → c.b7 = true → c.b3 = false → c.b1 = true → c.b6 = false → c.b10 = true → f c = true
def Law116 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b9 = false → c.b12 = true → c.b1 = false → c.b6 = true → c.b7 = false → c.b16 = false → c.b3 = false → f c = true
def Law117 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b17 = false → c.b4 = true → c.b1 = true → c.b7 = true → c.b3 = true → c.b10 = true → c.b6 = false → c.b13 = true → f c = true
def Law118 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b1 = true → c.b10 = false → c.b13 = false → c.b12 = false → c.b17 = false → c.b4 = true → c.b3 = false → c.b2 = true → c.b6 = true → c.b15 = true → f c = true
def Law119 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b17 = true → c.b2 = false → c.b12 = true → c.b7 = true → c.b14 = true → c.b0 = false → c.b1 = true → c.b6 = false → c.b5 = true → c.b16 = true → f c = true
def Law120 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b9 = true → c.b1 = true → c.b8 = true → c.b12 = true → c.b7 = false → c.b10 = false → c.b6 = true → c.b0 = false → c.b11 = true → c.b4 = true → c.b3 = false → f c = true
def Law121 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b3 = false → c.b10 = true → c.b16 = false → c.b6 = false → c.b1 = true → c.b11 = true → c.b5 = true → c.b4 = true → c.b12 = true → c.b7 = true → c.b0 = false → c.b17 = false → f c = false
def Law122 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b16 = true → c.b17 = false → c.b5 = false → c.b8 = true → c.b2 = false → c.b14 = false → c.b7 = false → c.b1 = true → c.b6 = false → c.b0 = false → c.b12 = true → f c = true
def Law123 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b6 = false → c.b7 = true → c.b17 = false → c.b12 = true → c.b2 = false → c.b1 = true → c.b13 = true → c.b0 = false → c.b10 = false → c.b9 = false → f c = true
def Law124 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b10 = true → c.b8 = true → c.b7 = false → c.b4 = false → c.b0 = false → c.b6 = false → c.b1 = true → c.b12 = true → c.b5 = true → c.b14 = true → f c = true
def Law125 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b1 = true → c.b12 = true → c.b0 = false → c.b2 = false → c.b16 = false → c.b15 = true → c.b6 = false → c.b10 = false → c.b8 = true → c.b5 = false → c.b17 = true → f c = true
def Law126 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b3 = false → c.b2 = true → c.b15 = true → c.b12 = true → c.b13 = true → c.b1 = true → c.b4 = true → c.b8 = false → c.b6 = false → c.b0 = false → c.b14 = true → c.b17 = true → c.b11 = false → c.b5 = true → c.b7 = true → f c = false
def Law127 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b5 = false → c.b12 = true → c.b8 = false → c.b6 = false → c.b17 = false → c.b16 = true → c.b3 = false → c.b10 = true → c.b1 = true → c.b0 = false → c.b7 = true → c.b14 = true → f c = true
def Law128 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b11 = true → c.b10 = false → c.b0 = false → c.b8 = false → c.b3 = false → c.b6 = true → c.b4 = true → c.b5 = false → c.b16 = true → c.b17 = false → c.b14 = false → c.b15 = true → c.b12 = true → c.b7 = false → c.b9 = true → c.b13 = true → f c = true
def Law129 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b7 = false → c.b1 = true → c.b6 = true → c.b4 = true → c.b16 = false → c.b13 = false → c.b10 = true → c.b2 = false → f c = false
def Law130 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b7 = false → c.b0 = false → c.b1 = false → c.b9 = false → c.b16 = false → c.b12 = false → c.b6 = true → f c = true
def Law131 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b2 = false → c.b10 = false → c.b6 = false → c.b0 = false → c.b15 = false → c.b12 = true → c.b1 = true → c.b17 = false → c.b7 = true → c.b9 = true → f c = true
def Law132 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b12 = false → c.b7 = false → c.b8 = true → c.b6 = false → c.b0 = true → c.b10 = true → c.b1 = true → f c = false
def Law133 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b3 = true → c.b6 = true → c.b10 = false → c.b14 = false → c.b12 = false → c.b15 = false → c.b0 = false → c.b1 = true → f c = true
def Law134 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b6 = true → c.b14 = false → c.b10 = true → c.b1 = true → c.b11 = true → c.b9 = false → c.b0 = true → c.b3 = true → f c = true
def Law135 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b10 = false → c.b15 = false → c.b17 = true → c.b9 = true → c.b0 = false → c.b6 = true → c.b14 = false → c.b16 = true → c.b12 = false → c.b1 = true → f c = false
def Law136 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b7 = false → c.b1 = true → c.b9 = false → c.b11 = true → c.b6 = true → c.b13 = false → c.b10 = false → f c = true
def Law137 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b4 = false → c.b9 = false → c.b1 = true → c.b14 = false → c.b16 = true → c.b11 = true → c.b7 = false → c.b2 = true → c.b15 = true → c.b0 = true → c.b5 = false → c.b6 = false → f c = false
def Law138 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b1 = true → c.b16 = true → c.b7 = false → c.b0 = false → c.b17 = false → c.b3 = false → c.b2 = true → c.b4 = false → c.b15 = false → c.b12 = true → c.b8 = true → c.b14 = false → c.b9 = true → c.b6 = false → c.b10 = false → f c = true
def Law139 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b9 = true → c.b10 = false → c.b3 = true → c.b13 = false → c.b6 = false → c.b11 = false → c.b1 = true → c.b12 = true → c.b17 = false → c.b0 = false → c.b8 = false → c.b7 = true → c.b15 = true → f c = false
def Law140 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b15 = false → c.b7 = false → c.b17 = true → c.b2 = false → c.b0 = false → c.b14 = false → c.b8 = true → c.b10 = true → c.b12 = true → c.b5 = false → c.b16 = true → c.b9 = false → c.b6 = false → f c = true
def Law141 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = false → c.b0 = false → c.b3 = false → c.b5 = true → c.b17 = true → c.b7 = true → c.b14 = false → c.b6 = false → c.b10 = true → c.b1 = true → f c = true
def Law142 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b10 = false → c.b6 = false → c.b16 = false → c.b11 = true → c.b7 = true → c.b17 = false → c.b12 = true → c.b0 = false → c.b1 = true → f c = true
def Law143 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b12 = true → c.b8 = false → c.b1 = true → c.b15 = true → c.b6 = false → c.b0 = false → c.b7 = true → c.b16 = true → c.b10 = false → c.b17 = false → f c = false
def Law144 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b6 = false → c.b7 = true → c.b3 = true → c.b0 = false → c.b1 = true → c.b5 = true → c.b14 = false → c.b17 = true → c.b4 = false → f c = true
def Law145 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = true → c.b11 = false → c.b3 = false → c.b10 = true → c.b8 = true → c.b6 = true → c.b1 = true → c.b14 = false → c.b4 = false → c.b13 = true → c.b7 = true → c.b9 = true → f c = false
def Law146 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b13 = true → c.b9 = true → c.b0 = false → c.b7 = true → c.b6 = false → c.b5 = false → c.b2 = false → c.b17 = false → c.b11 = false → c.b10 = false → c.b12 = true → c.b1 = true → f c = false
def Law147 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b17 = false → c.b5 = false → c.b0 = false → c.b14 = false → c.b11 = false → c.b16 = true → c.b8 = false → c.b4 = true → c.b2 = true → c.b9 = true → c.b12 = true → c.b7 = true → c.b3 = false → c.b15 = true → c.b13 = true → c.b10 = false → c.b6 = true → f c = true
def Law148 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b12 = true → c.b1 = true → c.b6 = false → c.b9 = false → c.b3 = false → c.b17 = false → c.b16 = false → c.b13 = false → c.b14 = false → c.b0 = false → c.b11 = false → c.b15 = false → c.b7 = true → c.b5 = true → c.b8 = true → c.b4 = true → f c = true
def Law149 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b2 = true → c.b13 = true → c.b12 = true → c.b3 = false → c.b0 = false → c.b4 = false → c.b11 = true → c.b16 = true → c.b10 = false → c.b14 = true → c.b1 = true → c.b17 = true → c.b8 = false → c.b6 = false → c.b9 = false → c.b7 = true → f c = true
def Law150 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b5 = true → c.b1 = true → c.b10 = true → c.b7 = false → c.b15 = false → c.b11 = false → c.b14 = false → c.b0 = true → c.b6 = true → c.b8 = true → c.b9 = true → c.b16 = false → f c = false
def Law151 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b14 = true → c.b13 = true → c.b17 = true → c.b15 = false → c.b3 = false → c.b7 = true → c.b2 = true → c.b11 = false → c.b5 = true → c.b0 = false → c.b12 = true → c.b16 = true → c.b8 = false → c.b1 = true → f c = true
def Law152 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b1 = true → c.b7 = false → c.b8 = true → c.b5 = false → c.b15 = true → c.b4 = true → c.b10 = false → c.b12 = true → c.b14 = false → c.b9 = true → c.b0 = false → f c = false
def Law153 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b17 = true → c.b6 = true → c.b10 = false → c.b8 = false → c.b9 = true → c.b12 = false → c.b4 = false → c.b14 = true → c.b1 = true → c.b0 = false → c.b15 = false → c.b11 = true → c.b5 = false → f c = false
def Law154 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b9 = false → c.b4 = false → c.b0 = true → c.b1 = true → c.b6 = false → c.b14 = false → c.b2 = true → c.b5 = false → c.b15 = false → c.b8 = true → c.b10 = false → c.b7 = false → f c = true
def Law155 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b14 = true → c.b16 = true → c.b0 = false → c.b2 = true → c.b11 = true → c.b6 = false → c.b7 = true → c.b13 = true → c.b1 = true → c.b10 = false → c.b8 = false → c.b5 = true → c.b4 = true → c.b3 = false → c.b12 = true → c.b17 = true → f c = false
def Law156 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b12 = true → c.b8 = true → c.b6 = false → c.b4 = false → c.b16 = true → c.b15 = true → c.b7 = false → c.b14 = false → c.b9 = false → c.b0 = false → c.b17 = true → f c = true
def Law157 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b16 = true → c.b10 = true → c.b6 = false → c.b0 = false → c.b9 = true → c.b5 = false → c.b8 = true → c.b7 = true → c.b4 = false → c.b14 = false → c.b12 = true → c.b17 = false → c.b3 = false → f c = true
def Law158 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b4 = false → c.b12 = false → c.b6 = false → c.b1 = true → c.b0 = false → f c = true
def Law159 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b1 = true → c.b17 = false → c.b16 = true → c.b12 = false → c.b6 = false → c.b0 = false → f c = false
def Law160 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b0 = false → c.b8 = false → c.b12 = true → c.b17 = false → c.b6 = false → c.b10 = true → c.b5 = true → c.b16 = false → c.b11 = false → c.b3 = false → c.b7 = true → c.b13 = false → c.b1 = true → f c = true
def Law161 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b0 = true → c.b8 = false → c.b2 = false → c.b15 = true → c.b1 = true → c.b7 = true → c.b11 = true → c.b10 = true → c.b4 = false → c.b14 = false → f c = true
def Law162 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b10 = true → c.b7 = true → c.b9 = false → c.b12 = true → c.b14 = true → c.b3 = false → c.b11 = true → c.b1 = true → c.b17 = false → c.b5 = false → c.b13 = true → c.b15 = true → c.b0 = false → c.b6 = false → f c = true
def Law163 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b16 = true → c.b13 = false → c.b10 = true → c.b6 = true → c.b0 = false → c.b4 = false → f c = true
def Law164 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b12 = true → c.b17 = false → c.b5 = false → c.b6 = true → c.b0 = false → c.b2 = true → c.b1 = true → c.b4 = true → c.b3 = false → c.b14 = true → c.b9 = true → c.b15 = true → f c = false
def Law165 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b17 = false → c.b8 = true → c.b1 = true → c.b15 = true → c.b0 = false → c.b6 = true → c.b4 = true → c.b10 = false → c.b13 = true → c.b2 = true → c.b16 = false → c.b12 = false → c.b9 = true → c.b5 = true → f c = true
def Law166 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b0 = false → c.b12 = true → c.b9 = false → c.b15 = false → c.b17 = false → c.b13 = false → c.b11 = false → c.b6 = false → c.b16 = false → c.b8 = false → c.b1 = true → c.b10 = false → c.b2 = false → c.b7 = true → f c = false
def Law167 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b11 = true → c.b9 = false → c.b13 = true → c.b7 = false → c.b12 = true → c.b1 = true → c.b0 = false → c.b2 = true → c.b10 = false → f c = true
def Law168 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b0 = true → c.b1 = true → c.b7 = true → c.b9 = true → c.b11 = true → c.b14 = false → c.b4 = true → c.b6 = true → c.b17 = true → c.b10 = true → c.b3 = true → c.b8 = true → c.b13 = true → f c = false
def Law169 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b0 = false → c.b6 = true → c.b14 = true → c.b8 = true → c.b17 = true → c.b1 = true → c.b5 = false → c.b4 = false → c.b16 = true → c.b10 = false → c.b12 = false → f c = false
def Law170 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b10 = true → c.b4 = false → c.b7 = true → c.b0 = false → c.b16 = true → c.b1 = true → c.b13 = true → c.b3 = true → f c = false
def Law171 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b3 = true → c.b8 = true → c.b10 = true → c.b9 = true → c.b13 = false → c.b0 = true → c.b7 = true → c.b6 = true → c.b14 = false → c.b1 = true → f c = true
def Law172 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b0 = false → c.b5 = false → c.b7 = true → c.b8 = false → c.b10 = true → c.b12 = true → c.b16 = true → c.b6 = false → c.b17 = false → c.b3 = false → c.b4 = true → f c = false
def Law173 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b6 = false → c.b11 = true → c.b9 = false → c.b14 = false → c.b0 = true → c.b1 = true → c.b3 = true → c.b4 = false → c.b8 = false → c.b7 = false → c.b10 = false → c.b16 = true → f c = false
def Law174 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b1 = true → c.b10 = true → c.b17 = false → c.b5 = false → c.b3 = false → c.b6 = false → c.b14 = false → c.b8 = false → c.b16 = true → c.b7 = true → c.b0 = false → c.b12 = true → f c = false
def Law175 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b0 = true → c.b11 = true → c.b10 = true → c.b12 = true → c.b8 = true → c.b1 = true → c.b5 = false → c.b17 = true → c.b13 = true → c.b9 = true → c.b6 = true → c.b16 = false → c.b7 = false → f c = true
def Law176 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b14 = true → c.b10 = true → c.b1 = true → c.b9 = true → c.b4 = false → c.b7 = true → c.b16 = true → c.b0 = false → c.b5 = false → c.b17 = false → c.b8 = true → c.b12 = true → c.b6 = false → f c = true
def Law177 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b2 = true → c.b13 = true → c.b4 = true → c.b7 = false → c.b12 = true → c.b9 = false → c.b11 = false → c.b10 = false → c.b0 = false → c.b14 = false → c.b16 = true → c.b6 = false → c.b17 = true → c.b1 = true → f c = true
def Law178 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b0 = false → c.b9 = true → c.b6 = true → c.b3 = false → c.b15 = false → c.b7 = true → c.b11 = true → c.b17 = false → c.b12 = true → c.b10 = false → c.b1 = true → f c = false
def Law179 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b12 = true → c.b4 = false → c.b10 = true → c.b13 = true → c.b6 = false → c.b5 = true → c.b14 = true → c.b7 = true → c.b3 = false → c.b11 = false → c.b17 = false → c.b0 = false → c.b16 = true → f c = true
def Law180 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b7 = false → c.b6 = true → c.b0 = false → c.b16 = true → c.b13 = true → c.b1 = true → c.b4 = false → f c = false
def Law181 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b5 = false → c.b11 = true → c.b16 = true → c.b17 = true → c.b1 = false → f c = false
def Law182 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b5 = true → c.b1 = false → c.b11 = true → c.b16 = true → c.b7 = true → c.b3 = true → c.b0 = false → f c = true
def Law183 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b17 = true → c.b8 = true → c.b0 = true → c.b2 = true → c.b6 = true → c.b3 = false → c.b10 = true → c.b9 = true → c.b14 = false → c.b1 = true → c.b13 = false → f c = false
def Law184 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b10 = false → c.b1 = true → c.b7 = false → c.b3 = true → c.b14 = true → c.b12 = true → c.b0 = false → f c = false
def Law185 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b16 = false → c.b14 = true → c.b0 = false → c.b5 = true → c.b9 = false → c.b13 = true → c.b6 = false → c.b17 = false → c.b11 = true → c.b4 = false → c.b15 = true → c.b10 = true → c.b1 = true → c.b7 = true → c.b12 = true → f c = true
def Law186 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b0 = false → c.b14 = true → c.b13 = false → c.b1 = true → c.b17 = true → c.b5 = false → c.b10 = true → c.b12 = true → c.b6 = false → c.b7 = false → f c = false
def Law187 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b15 = false → c.b14 = true → c.b1 = true → c.b7 = true → c.b0 = true → f c = true
def Law188 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b11 = false → c.b16 = false → c.b12 = true → c.b1 = true → c.b7 = true → c.b8 = true → c.b6 = false → c.b10 = true → c.b9 = true → c.b17 = false → c.b0 = false → f c = false
def Law189 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b12 = true → c.b14 = false → c.b8 = true → c.b17 = true → c.b6 = false → c.b1 = true → c.b10 = false → c.b0 = false → c.b13 = true → c.b7 = false → c.b11 = true → c.b2 = true → f c = true
def Law190 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b3 = false → c.b6 = false → c.b5 = true → c.b14 = false → c.b10 = true → c.b16 = true → c.b17 = false → c.b7 = true → c.b12 = true → c.b1 = true → f c = false
def Law191 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b13 = false → c.b9 = true → c.b7 = true → c.b11 = true → c.b0 = true → c.b6 = true → c.b2 = false → c.b3 = true → c.b10 = true → c.b14 = false → c.b1 = true → f c = false
def Law192 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b10 = false → c.b16 = false → c.b7 = true → c.b17 = false → c.b8 = true → c.b15 = true → c.b2 = false → c.b12 = true → c.b13 = false → c.b6 = false → c.b3 = true → c.b9 = true → c.b14 = true → c.b11 = false → c.b1 = true → f c = false
def Law193 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = true → c.b6 = true → c.b10 = false → c.b0 = false → c.b3 = false → c.b16 = true → c.b15 = true → c.b1 = true → c.b11 = false → c.b13 = false → c.b5 = false → c.b8 = false → c.b17 = false → c.b4 = true → c.b14 = false → c.b2 = false → c.b7 = true → f c = true
def Law194 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b0 = false → c.b14 = false → c.b11 = true → c.b7 = true → c.b5 = false → c.b12 = true → c.b2 = true → c.b8 = false → c.b1 = true → c.b6 = true → c.b4 = true → c.b17 = true → c.b15 = true → c.b3 = false → c.b10 = false → c.b9 = true → f c = true
def Law195 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b0 = false → c.b8 = true → c.b1 = true → c.b16 = false → c.b10 = true → c.b4 = false → f c = false
def Law196 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b4 = true → c.b0 = false → c.b12 = true → c.b5 = false → c.b2 = false → c.b6 = true → c.b1 = true → c.b10 = false → c.b3 = true → c.b9 = true → c.b14 = true → f c = false
def Law197 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b6 = true → c.b15 = false → c.b0 = false → c.b1 = true → c.b12 = true → c.b16 = false → c.b8 = true → c.b10 = false → c.b5 = false → c.b2 = false → c.b9 = true → f c = false
def Law198 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b4 = false → c.b14 = false → c.b8 = true → c.b16 = false → c.b1 = true → c.b7 = true → c.b0 = true → f c = false
def Law199 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b2 = false → c.b1 = true → c.b8 = true → c.b9 = false → c.b0 = true → c.b4 = false → c.b14 = false → c.b6 = false → c.b16 = true → c.b7 = false → f c = false
def Law200 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b0 = true → c.b13 = true → c.b10 = true → c.b17 = true → c.b4 = true → c.b8 = true → c.b9 = true → c.b14 = false → c.b11 = true → c.b12 = false → c.b2 = true → c.b1 = true → c.b6 = true → c.b3 = false → f c = true
def Law201 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b5 = true → c.b6 = true → c.b16 = true → c.b1 = false → c.b3 = true → f c = false
def Law202 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b11 = true → c.b17 = false → c.b0 = false → c.b16 = false → c.b10 = true → c.b14 = true → c.b3 = false → c.b1 = true → c.b7 = true → c.b13 = false → c.b12 = true → c.b9 = false → f c = true
def Law203 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b6 = true → c.b9 = true → c.b1 = true → c.b15 = false → c.b2 = false → c.b14 = false → c.b0 = false → c.b11 = true → c.b8 = false → c.b4 = true → c.b16 = false → c.b7 = false → c.b10 = false → f c = true
def Law204 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b5 = true → c.b14 = false → c.b3 = false → c.b6 = false → c.b0 = true → c.b1 = true → c.b15 = false → c.b4 = true → c.b12 = true → c.b7 = true → f c = true
def Law205 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b6 = false → c.b14 = false → c.b16 = true → c.b1 = true → c.b10 = false → c.b0 = true → c.b7 = false → f c = true
def Law206 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b16 = false → c.b7 = false → c.b4 = true → c.b12 = false → c.b14 = false → c.b13 = true → c.b0 = true → c.b10 = true → c.b6 = true → c.b9 = true → c.b11 = true → c.b15 = false → c.b8 = true → c.b1 = true → f c = true
def Law207 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b9 = true → c.b10 = true → c.b0 = true → c.b6 = true → c.b8 = true → c.b1 = true → c.b11 = true → c.b13 = false → c.b14 = false → c.b12 = true → c.b16 = false → f c = false
def Law208 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b8 = true → c.b11 = false → c.b2 = true → c.b0 = false → c.b5 = false → c.b1 = true → c.b10 = false → c.b9 = true → c.b15 = false → c.b16 = false → c.b6 = true → f c = true
def Law209 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b4 = true → c.b15 = true → c.b10 = false → c.b14 = true → c.b9 = true → c.b11 = true → c.b0 = false → c.b3 = false → c.b12 = true → c.b1 = true → c.b17 = true → c.b6 = true → c.b2 = true → f c = false
def Law210 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b0 = false → c.b17 = true → c.b6 = true → c.b12 = false → c.b16 = false → c.b4 = false → c.b15 = false → c.b10 = false → c.b9 = true → c.b13 = false → f c = false
def Law211 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b13 = false → c.b1 = true → c.b17 = false → c.b15 = true → c.b7 = true → c.b11 = false → c.b16 = true → c.b8 = true → c.b6 = false → c.b12 = true → c.b0 = false → c.b10 = false → c.b2 = false → f c = false
def Law212 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b15 = false → c.b4 = false → c.b8 = true → c.b7 = false → c.b0 = false → c.b9 = false → c.b2 = true → c.b6 = false → c.b16 = true → c.b17 = false → c.b1 = true → c.b14 = false → f c = false
def Law213 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b4 = false → c.b2 = true → c.b17 = true → c.b0 = false → c.b5 = false → c.b14 = true → c.b10 = false → c.b6 = false → c.b7 = true → c.b12 = true → c.b1 = true → f c = true
def Law214 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b1 = true → c.b0 = false → c.b3 = true → c.b17 = false → c.b6 = false → c.b16 = true → c.b8 = true → c.b12 = true → c.b7 = true → c.b10 = false → f c = false
def Law215 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b15 = true → c.b0 = false → c.b8 = false → c.b12 = false → c.b10 = false → c.b1 = true → c.b17 = false → c.b13 = true → c.b4 = true → c.b3 = false → c.b6 = true → f c = false
def Law216 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b14 = false → c.b2 = false → c.b0 = false → c.b4 = true → c.b16 = true → c.b11 = true → c.b12 = true → c.b7 = true → c.b1 = true → c.b15 = true → c.b10 = false → c.b8 = false → c.b5 = false → c.b6 = true → c.b13 = true → c.b3 = false → f c = false
def Law217 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b5 = false → c.b17 = false → c.b9 = true → c.b10 = true → c.b0 = true → c.b3 = true → c.b16 = false → c.b7 = true → c.b2 = true → c.b14 = false → c.b1 = true → c.b6 = true → f c = false
def Law218 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b3 = true → c.b11 = false → c.b9 = true → c.b15 = true → c.b14 = false → c.b1 = false → f c = true
def Law219 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b17 = false → c.b12 = true → c.b3 = true → c.b16 = true → c.b14 = false → c.b9 = true → c.b0 = false → c.b6 = false → c.b5 = false → c.b8 = true → c.b2 = true → c.b4 = false → c.b7 = false → c.b1 = true → f c = false
def Law220 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b13 = false → c.b1 = true → c.b4 = false → c.b17 = false → c.b6 = false → c.b12 = true → c.b11 = false → c.b10 = true → c.b5 = true → c.b0 = false → c.b3 = false → c.b14 = true → c.b16 = true → f c = false
def Law221 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b15 = false → c.b13 = false → c.b7 = true → c.b12 = true → c.b5 = false → c.b17 = false → c.b10 = true → c.b6 = false → c.b8 = true → c.b2 = false → c.b1 = true → c.b3 = false → c.b16 = true → c.b0 = false → f c = true
def Law222 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b17 = true → c.b6 = false → c.b4 = true → c.b1 = true → c.b0 = false → c.b16 = true → f c = false
def Law223 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b11 = true → c.b0 = true → c.b6 = true → c.b3 = true → c.b10 = true → c.b7 = true → c.b1 = true → c.b13 = false → c.b2 = true → c.b9 = true → c.b14 = false → f c = false
def Law224 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b13 = false → c.b15 = false → c.b11 = false → c.b6 = false → c.b10 = true → c.b4 = false → c.b7 = false → c.b9 = true → c.b8 = true → c.b14 = false → c.b0 = false → c.b16 = true → c.b17 = false → c.b3 = false → c.b12 = true → c.b2 = true → f c = false
def Law225 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b17 = true → c.b7 = false → c.b1 = true → c.b2 = true → c.b10 = true → c.b8 = true → c.b13 = false → c.b6 = false → c.b0 = false → c.b14 = false → c.b16 = true → c.b5 = true → c.b12 = true → f c = false
def Law226 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b12 = true → c.b4 = true → c.b5 = true → c.b2 = true → c.b3 = false → c.b15 = true → c.b14 = true → c.b0 = false → c.b9 = true → c.b6 = true → c.b13 = true → c.b1 = true → c.b10 = false → f c = true
def Law227 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b1 = true → c.b9 = true → c.b11 = false → c.b4 = false → c.b0 = true → c.b8 = true → c.b13 = true → c.b10 = true → c.b7 = true → c.b14 = false → c.b6 = true → f c = false
def Law228 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b10 = true → c.b9 = true → c.b8 = false → c.b2 = false → c.b7 = false → c.b6 = true → c.b4 = true → c.b14 = false → c.b0 = true → f c = false
def Law229 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b15 = true → c.b7 = true → c.b6 = false → c.b2 = false → c.b3 = false → c.b12 = true → c.b8 = false → c.b1 = true → c.b10 = false → c.b9 = true → c.b13 = false → c.b0 = false → c.b11 = false → f c = true
def Law230 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b15 = true → c.b2 = true → c.b3 = false → c.b12 = true → c.b11 = false → c.b8 = true → c.b6 = false → c.b0 = false → c.b7 = true → c.b13 = true → c.b4 = true → c.b14 = true → c.b16 = true → c.b5 = true → c.b17 = true → c.b1 = true → f c = true
def Law231 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b12 = true → c.b11 = false → c.b0 = false → c.b9 = false → c.b6 = true → c.b15 = false → c.b10 = false → c.b1 = true → c.b14 = false → f c = false
def Law232 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b15 = false → c.b0 = true → c.b5 = false → c.b14 = false → c.b6 = false → c.b9 = false → c.b4 = false → c.b8 = false → c.b10 = false → c.b7 = false → c.b16 = true → c.b1 = true → f c = true
def Law233 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b3 = true → c.b0 = false → c.b14 = false → c.b6 = true → c.b9 = true → c.b5 = false → c.b7 = false → c.b15 = true → c.b1 = true → c.b12 = true → c.b4 = true → c.b8 = false → f c = false
def Law234 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b5 = false → c.b0 = false → c.b10 = false → c.b11 = false → c.b8 = false → c.b15 = false → c.b1 = true → c.b17 = true → c.b13 = false → c.b14 = true → c.b4 = false → c.b16 = true → c.b6 = true → c.b12 = false → f c = true
def Law235 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b0 = false → c.b11 = false → c.b2 = true → c.b6 = false → c.b4 = false → c.b12 = true → c.b16 = true → c.b13 = true → c.b9 = false → c.b17 = true → c.b1 = true → c.b14 = false → c.b8 = true → c.b10 = false → f c = false
def Law236 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b3 = true → c.b6 = false → c.b7 = true → c.b14 = false → c.b5 = true → c.b17 = true → c.b12 = true → c.b1 = true → c.b4 = true → f c = false
def Law237 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b1 = true → c.b6 = true → c.b7 = false → c.b10 = true → c.b13 = true → c.b16 = false → c.b2 = false → c.b4 = true → f c = false
def Law238 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b5 = true → c.b11 = true → c.b7 = false → c.b1 = false → c.b3 = true → c.b6 = false → f c = true
def Law239 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b10 = false → c.b1 = true → c.b2 = false → c.b6 = false → c.b11 = false → c.b16 = false → c.b13 = false → c.b9 = false → c.b0 = false → c.b12 = true → c.b8 = true → c.b17 = false → c.b7 = true → f c = true
def Law240 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b14 = false → c.b4 = false → c.b7 = true → c.b15 = true → c.b1 = true → c.b6 = false → c.b0 = true → c.b5 = false → c.b3 = false → c.b10 = true → c.b8 = false → f c = false
def Law241 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b6 = true → c.b8 = true → c.b1 = true → c.b0 = true → c.b9 = true → c.b11 = false → c.b10 = true → c.b5 = false → c.b14 = false → c.b15 = false → c.b4 = true → c.b7 = false → f c = true
def Law242 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b6 = true → c.b5 = false → c.b0 = false → c.b8 = false → c.b11 = false → c.b4 = false → c.b16 = true → c.b17 = true → c.b14 = true → c.b10 = false → c.b1 = true → c.b9 = true → c.b15 = false → c.b12 = false → f c = true
def Law243 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b4 = false → c.b7 = false → c.b13 = true → c.b17 = true → c.b3 = false → c.b1 = false → c.b16 = false → f c = false
def Law244 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b12 = true → c.b16 = true → c.b1 = true → c.b2 = true → c.b8 = true → c.b7 = false → c.b6 = false → c.b13 = false → c.b14 = false → c.b4 = true → c.b11 = false → c.b17 = true → f c = true
def Law245 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b7 = true → c.b1 = true → c.b11 = true → c.b0 = false → c.b12 = true → c.b3 = false → c.b16 = false → c.b10 = true → c.b9 = true → c.b6 = false → c.b5 = true → c.b17 = false → f c = false
def Law246 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b10 = false → c.b0 = false → c.b1 = true → c.b16 = true → c.b4 = true → c.b6 = true → c.b12 = false → c.b3 = true → c.b17 = true → c.b2 = false → c.b14 = true → f c = false
def Law247 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b6 = false → c.b12 = false → c.b17 = true → c.b16 = true → c.b0 = false → c.b4 = false → c.b1 = true → f c = false
def Law248 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b7 = true → c.b5 = false → c.b3 = true → c.b6 = false → c.b14 = false → c.b16 = false → c.b0 = true → c.b11 = false → c.b10 = true → c.b13 = true → c.b4 = false → c.b15 = true → c.b8 = false → f c = false
def Law249 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b16 = true → c.b1 = true → c.b0 = false → c.b12 = true → c.b9 = true → c.b10 = false → c.b6 = true → c.b8 = false → c.b15 = false → f c = false
def Law250 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b8 = false → c.b7 = false → c.b10 = true → c.b12 = false → c.b6 = false → c.b1 = true → c.b0 = true → f c = true
def Law251 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b0 = true → c.b6 = true → c.b1 = true → c.b8 = false → c.b14 = false → c.b2 = true → c.b7 = true → c.b5 = false → c.b10 = true → c.b16 = false → c.b3 = false → f c = true
def Law252 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b0 = false → c.b16 = false → c.b14 = true → c.b11 = true → c.b6 = false → c.b12 = false → c.b4 = true → f c = true
def Law253 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b3 = true → c.b1 = true → c.b0 = false → c.b2 = true → c.b8 = true → c.b15 = false → c.b4 = false → c.b5 = true → c.b9 = true → c.b12 = true → c.b14 = false → c.b7 = false → c.b6 = false → c.b17 = false → f c = true
def Law254 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b10 = true → c.b6 = true → c.b4 = true → c.b16 = false → c.b0 = false → c.b7 = false → c.b2 = true → f c = true
def Law255 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b6 = false → c.b12 = false → c.b14 = false → c.b1 = true → c.b7 = true → c.b0 = true → c.b3 = false → c.b4 = true → c.b15 = true → c.b9 = false → f c = false
def Law256 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b14 = false → c.b0 = false → c.b10 = false → c.b9 = true → c.b8 = false → c.b4 = true → c.b5 = false → c.b16 = false → c.b7 = true → c.b1 = true → c.b12 = true → c.b6 = true → c.b3 = true → f c = true
def Law257 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b17 = true → c.b11 = true → c.b10 = false → c.b3 = false → c.b0 = false → c.b5 = false → c.b9 = true → c.b16 = true → c.b7 = false → c.b14 = false → c.b6 = true → c.b1 = true → c.b12 = true → c.b4 = true → c.b13 = true → c.b15 = true → f c = false
def Law258 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b11 = true → c.b16 = false → c.b3 = true → c.b14 = false → f c = false
def Law259 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b2 = true → c.b7 = true → c.b1 = true → c.b0 = false → c.b6 = false → c.b3 = false → c.b14 = true → c.b12 = true → c.b17 = true → c.b10 = true → c.b16 = true → c.b5 = true → c.b4 = true → c.b13 = true → f c = true
def Law260 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = false → c.b0 = true → c.b6 = false → c.b16 = false → c.b7 = false → c.b1 = true → c.b10 = false → f c = false
def Law261 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b14 = false → c.b11 = false → c.b0 = false → c.b17 = false → c.b10 = true → c.b3 = false → c.b7 = true → c.b1 = true → c.b9 = false → c.b5 = false → c.b16 = false → c.b6 = false → c.b12 = true → c.b8 = true → f c = true
def Law262 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b0 = false → c.b1 = true → c.b3 = false → c.b14 = false → c.b6 = false → c.b5 = true → c.b10 = true → c.b12 = true → c.b7 = true → c.b9 = true → f c = true
def Law263 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b2 = false → c.b9 = true → c.b6 = true → c.b14 = false → c.b10 = true → c.b8 = false → c.b1 = true → c.b3 = true → c.b0 = true → f c = true
def Law264 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b13 = false → c.b0 = false → c.b4 = true → c.b15 = true → c.b1 = true → c.b12 = true → c.b6 = true → c.b14 = true → c.b3 = false → c.b5 = true → c.b2 = true → c.b10 = false → c.b17 = false → f c = false
def Law265 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b10 = false → c.b11 = true → c.b3 = false → c.b1 = true → c.b8 = true → c.b2 = true → c.b12 = true → c.b16 = true → c.b17 = false → c.b7 = true → c.b0 = false → f c = false
def Law266 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b3 = true → c.b1 = false → c.b14 = true → c.b11 = false → f c = false
def Law267 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b6 = false → c.b1 = true → c.b16 = true → c.b0 = true → c.b11 = false → c.b10 = false → c.b14 = false → c.b9 = false → c.b2 = true → c.b4 = false → c.b5 = false → c.b15 = true → f c = false
def Law268 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b6 = false → c.b17 = false → c.b1 = true → c.b0 = false → c.b9 = false → c.b12 = false → c.b15 = true → c.b16 = true → c.b7 = true → f c = false
def Law269 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b0 = false → c.b16 = false → c.b10 = true → c.b12 = true → c.b13 = false → c.b14 = false → c.b6 = false → c.b17 = false → c.b11 = true → c.b1 = true → c.b7 = true → c.b3 = false → f c = false
def Law270 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b17 = true → c.b9 = true → c.b6 = true → c.b10 = false → c.b1 = true → c.b16 = false → c.b4 = false → c.b15 = true → c.b0 = false → f c = false
def Law271 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b13 = false → c.b12 = true → c.b15 = false → c.b2 = true → c.b9 = false → c.b7 = true → c.b6 = false → c.b8 = true → c.b5 = false → c.b1 = true → c.b17 = false → c.b3 = false → c.b16 = true → c.b10 = true → f c = true
def Law272 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b17 = true → c.b15 = true → c.b12 = true → c.b6 = false → c.b14 = true → c.b13 = false → c.b5 = true → c.b0 = false → c.b1 = true → f c = true
def Law273 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b11 = false → c.b8 = false → c.b6 = true → c.b9 = true → c.b16 = true → c.b2 = false → c.b10 = false → c.b15 = true → c.b14 = false → c.b4 = true → c.b12 = true → c.b13 = true → c.b7 = true → c.b5 = false → c.b3 = false → c.b1 = true → f c = true
def Law274 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b3 = false → c.b2 = false → c.b4 = true → c.b12 = false → c.b6 = true → c.b11 = true → c.b7 = true → c.b9 = true → c.b0 = true → c.b1 = true → c.b13 = true → c.b14 = false → c.b10 = true → c.b17 = true → f c = true
def Law275 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b6 = false → c.b3 = true → c.b11 = true → c.b16 = true → c.b1 = false → c.b5 = true → c.b2 = true → c.b0 = true → c.b8 = false → f c = false
def Law276 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b16 = false → c.b10 = false → c.b4 = true → c.b2 = false → c.b0 = false → c.b6 = true → c.b5 = true → c.b9 = true → c.b12 = true → c.b14 = true → c.b15 = true → f c = true
def Law277 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b5 = true → c.b15 = true → c.b10 = false → c.b17 = true → c.b6 = true → c.b12 = true → c.b11 = false → c.b0 = false → c.b9 = true → c.b4 = true → c.b1 = true → c.b3 = false → c.b2 = true → f c = true
def Law278 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b2 = true → c.b3 = false → c.b8 = false → c.b17 = true → c.b1 = true → c.b7 = true → c.b4 = false → c.b13 = true → c.b12 = true → c.b9 = true → c.b0 = false → c.b16 = true → c.b10 = false → c.b6 = false → c.b11 = true → c.b5 = true → f c = true
def Law279 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b16 = false → c.b8 = false → c.b4 = true → c.b7 = false → c.b10 = false → c.b0 = true → c.b1 = true → c.b14 = false → c.b5 = true → f c = false
def Law280 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b6 = false → c.b2 = false → c.b0 = false → c.b12 = true → c.b1 = true → c.b5 = true → c.b3 = false → c.b7 = true → c.b10 = false → c.b14 = false → f c = true
def Law281 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b15 = false → c.b4 = false → c.b6 = false → c.b0 = true → c.b7 = false → c.b2 = false → c.b1 = true → c.b16 = false → f c = true
def Law282 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b12 = false → c.b10 = false → c.b9 = true → c.b2 = false → c.b6 = true → c.b17 = true → c.b1 = true → c.b0 = false → c.b4 = true → c.b15 = true → f c = false
def Law283 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b3 = false → c.b2 = false → c.b10 = true → c.b6 = false → c.b0 = true → c.b1 = true → c.b14 = false → c.b15 = false → c.b4 = true → c.b7 = true → f c = false
def Law284 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b12 = true → c.b3 = false → c.b9 = false → c.b16 = false → c.b7 = false → c.b1 = false → c.b14 = true → f c = true
def Law285 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b1 = true → c.b6 = true → c.b4 = false → c.b10 = false → c.b16 = true → c.b3 = true → c.b9 = true → c.b0 = false → c.b12 = false → c.b17 = true → c.b14 = false → f c = false
def Law286 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b17 = false → c.b5 = false → c.b3 = true → c.b16 = true → c.b1 = false → f c = false
def Law287 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b4 = true → c.b12 = false → c.b13 = false → c.b7 = true → c.b14 = false → c.b1 = true → c.b0 = true → c.b15 = true → c.b3 = false → c.b9 = true → f c = true
def Law288 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b12 = true → c.b7 = true → c.b17 = true → c.b1 = true → c.b6 = false → c.b3 = true → c.b14 = true → c.b13 = true → c.b16 = true → c.b5 = true → c.b2 = true → f c = false
def Law289 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b9 = true → c.b11 = true → c.b15 = false → c.b1 = true → c.b12 = true → c.b3 = true → c.b6 = true → c.b7 = false → c.b8 = true → c.b4 = true → c.b0 = false → f c = true
def Law290 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b12 = false → c.b9 = false → c.b4 = false → c.b6 = true → c.b0 = false → c.b1 = true → c.b17 = true → f c = false
def Law291 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b14 = true → c.b13 = true → c.b9 = false → c.b1 = true → c.b15 = false → c.b3 = false → c.b8 = false → c.b10 = false → c.b12 = true → c.b17 = true → c.b0 = false → c.b16 = true → c.b7 = true → c.b11 = true → c.b4 = true → c.b5 = true → c.b2 = true → f c = true
def Law292 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b17 = true → c.b5 = false → c.b14 = true → c.b1 = true → c.b7 = false → c.b0 = false → c.b8 = false → c.b13 = true → c.b10 = true → c.b4 = true → c.b12 = true → f c = true
def Law293 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b4 = true → c.b3 = false → c.b14 = false → c.b1 = true → c.b6 = false → c.b15 = true → c.b12 = false → c.b13 = true → c.b0 = true → f c = false
def Law294 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b3 = true → c.b1 = false → c.b16 = true → f c = true
def Law295 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b0 = true → c.b1 = true → c.b7 = true → c.b13 = true → c.b10 = true → c.b4 = false → c.b15 = false → c.b6 = false → c.b14 = false → f c = false
def Law296 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b7 = true → c.b0 = true → c.b14 = false → c.b1 = true → c.b13 = false → c.b6 = false → c.b8 = false → c.b10 = true → c.b15 = false → f c = true
def Law297 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b2 = true → c.b1 = true → c.b10 = false → c.b4 = true → c.b12 = false → c.b0 = false → c.b8 = true → c.b9 = false → c.b15 = true → c.b17 = false → c.b13 = true → f c = false
def Law298 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b1 = false → c.b16 = false → c.b9 = true → c.b15 = false → c.b11 = false → c.b3 = true → f c = false
def Law299 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b1 = true → c.b14 = false → c.b12 = true → c.b9 = false → c.b6 = true → c.b10 = false → c.b11 = false → c.b15 = false → c.b13 = false → f c = true
def Law300 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b5 = true → c.b11 = true → c.b1 = true → c.b9 = false → c.b14 = false → c.b16 = false → c.b0 = true → c.b6 = true → f c = false
def Law301 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b1 = false → c.b3 = false → c.b6 = false → c.b13 = false → c.b16 = false → f c = false
def Law302 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b9 = false → c.b12 = false → c.b0 = true → c.b14 = false → c.b10 = true → c.b6 = false → c.b8 = true → c.b1 = true → f c = true
def Law303 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b9 = false → c.b16 = true → c.b2 = false → c.b11 = false → c.b6 = false → c.b7 = false → c.b5 = false → c.b17 = true → c.b12 = true → c.b0 = false → c.b15 = false → c.b10 = false → c.b14 = false → c.b3 = true → c.b1 = true → f c = true
def Law304 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b14 = false → c.b10 = true → c.b7 = true → c.b17 = false → c.b6 = false → c.b3 = false → c.b0 = false → c.b16 = false → c.b1 = true → c.b13 = true → c.b15 = false → c.b11 = true → c.b12 = true → f c = true
def Law305 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b13 = false → c.b9 = true → c.b4 = false → c.b3 = false → c.b6 = true → c.b10 = false → c.b1 = true → c.b0 = false → c.b8 = true → c.b11 = true → c.b7 = false → c.b15 = false → f c = false
def Law306 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b5 = true → c.b0 = true → c.b1 = false → c.b11 = true → c.b2 = false → c.b8 = true → c.b16 = true → c.b6 = false → c.b7 = true → f c = false
def Law307 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b6 = true → c.b7 = true → c.b11 = true → c.b12 = true → c.b1 = true → c.b0 = false → c.b15 = false → c.b10 = false → c.b3 = true → c.b8 = true → f c = true
def Law308 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b12 = true → c.b6 = true → c.b16 = false → c.b2 = false → c.b0 = false → c.b1 = true → c.b9 = true → c.b14 = true → c.b8 = false → c.b15 = false → c.b11 = true → f c = false
def Law309 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b10 = true → c.b1 = true → c.b12 = true → c.b14 = false → c.b2 = false → c.b0 = false → c.b8 = true → c.b16 = true → c.b7 = false → c.b9 = true → f c = true
def Law310 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b7 = true → c.b6 = true → c.b2 = false → c.b14 = false → c.b10 = false → c.b16 = true → c.b4 = true → c.b17 = true → c.b1 = true → c.b0 = false → f c = false
def Law311 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b2 = true → c.b8 = true → c.b13 = true → c.b16 = true → c.b0 = false → c.b9 = false → c.b17 = true → c.b12 = true → c.b5 = false → c.b3 = true → c.b11 = false → c.b14 = false → c.b7 = false → c.b6 = false → c.b1 = true → f c = false
def Law312 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b11 = false → c.b16 = true → c.b2 = false → c.b6 = true → c.b12 = true → c.b5 = true → c.b15 = true → c.b14 = true → c.b10 = false → c.b4 = true → c.b1 = true → c.b9 = true → f c = false
def Law313 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b1 = true → c.b7 = true → c.b4 = true → c.b5 = true → c.b17 = false → c.b16 = true → c.b10 = true → c.b6 = false → c.b0 = false → c.b3 = false → c.b14 = true → f c = false
def Law314 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b8 = false → c.b1 = true → c.b14 = true → c.b0 = false → c.b3 = true → c.b17 = true → c.b12 = true → c.b7 = false → c.b6 = false → c.b5 = false → c.b10 = true → f c = false
def Law315 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b16 = false → c.b0 = false → c.b13 = true → c.b12 = true → c.b14 = true → c.b1 = true → c.b5 = true → c.b7 = true → c.b17 = true → f c = true
def Law316 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b2 = true → c.b17 = true → c.b12 = true → c.b16 = true → c.b4 = true → c.b6 = true → c.b9 = true → c.b5 = false → c.b15 = true → c.b3 = false → c.b1 = true → c.b10 = false → c.b0 = false → f c = true
def Law317 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b1 = true → c.b11 = false → c.b10 = true → c.b0 = true → c.b17 = true → c.b9 = false → c.b14 = false → c.b6 = true → f c = false
def Law318 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b12 = true → c.b1 = true → c.b6 = true → c.b15 = true → c.b9 = true → c.b0 = false → c.b10 = false → f c = true
def Law319 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = true → c.b6 = false → c.b0 = false → c.b10 = true → c.b14 = false → c.b16 = true → c.b2 = true → c.b5 = false → c.b11 = true → c.b17 = true → c.b8 = true → c.b1 = true → c.b13 = false → c.b7 = false → f c = false
def Law320 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b13 = false → c.b0 = true → c.b16 = false → c.b1 = true → c.b6 = true → c.b12 = false → c.b8 = true → c.b10 = true → c.b14 = false → c.b11 = true → c.b9 = true → f c = true
def Law321 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b4 = false → c.b16 = false → c.b6 = false → c.b5 = false → c.b7 = true → c.b10 = true → c.b12 = true → c.b11 = true → c.b17 = false → c.b1 = true → c.b9 = true → c.b3 = false → f c = true
def Law322 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b0 = false → c.b5 = false → c.b3 = false → c.b15 = true → c.b13 = true → c.b14 = false → c.b7 = true → c.b4 = true → c.b10 = false → c.b6 = true → c.b17 = false → c.b12 = true → c.b2 = true → c.b9 = true → c.b16 = true → c.b8 = false → c.b1 = true → f c = false
def Law323 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b6 = false → c.b7 = false → c.b17 = true → c.b16 = true → c.b13 = true → c.b2 = true → c.b10 = true → c.b0 = false → c.b4 = false → c.b14 = false → c.b12 = true → c.b8 = true → c.b11 = true → f c = false
def Law324 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b11 = false → c.b5 = true → c.b9 = true → c.b15 = false → c.b10 = false → c.b1 = true → c.b8 = true → c.b16 = false → c.b6 = true → c.b4 = false → c.b0 = false → f c = true
def Law325 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b12 = true → c.b17 = true → c.b0 = false → c.b13 = true → c.b2 = true → c.b15 = true → c.b11 = true → c.b5 = false → c.b4 = true → c.b7 = true → c.b1 = true → c.b6 = false → f c = true
def Law326 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b17 = false → c.b7 = false → c.b12 = false → c.b0 = true → c.b16 = false → c.b14 = false → c.b10 = true → c.b1 = true → c.b13 = true → c.b8 = true → c.b6 = true → c.b11 = true → f c = false
def Law327 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b17 = false → c.b7 = true → c.b4 = true → c.b6 = false → c.b9 = false → c.b14 = false → c.b10 = true → c.b16 = false → c.b5 = true → c.b0 = false → c.b11 = false → c.b1 = true → c.b8 = true → c.b15 = false → c.b3 = false → c.b13 = true → f c = false
def Law328 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b8 = true → c.b12 = true → c.b13 = true → c.b1 = true → c.b3 = false → c.b10 = true → c.b0 = false → c.b9 = true → c.b5 = false → c.b16 = true → c.b4 = true → c.b17 = false → c.b7 = true → f c = true
def Law329 (f : Decide) : Prop := ∀ c : Case, c.b15 = false → c.b12 = true → c.b10 = false → c.b7 = false → c.b8 = true → c.b9 = true → c.b11 = true → c.b1 = true → c.b4 = false → c.b6 = true → c.b3 = true → c.b0 = false → f c = true
def Law330 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b13 = true → c.b1 = true → c.b12 = false → c.b15 = true → c.b0 = false → c.b17 = false → c.b2 = false → c.b6 = true → c.b10 = false → f c = false
def Law331 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b14 = false → c.b6 = false → c.b10 = false → c.b0 = false → c.b7 = false → c.b11 = true → c.b5 = false → c.b12 = true → c.b1 = true → c.b2 = true → c.b13 = false → c.b17 = true → c.b8 = true → f c = false
def Law332 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b0 = true → c.b3 = true → c.b16 = true → c.b2 = false → c.b5 = true → c.b8 = false → c.b6 = false → c.b1 = false → c.b11 = true → f c = true
def Law333 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b7 = false → c.b13 = true → c.b16 = false → c.b12 = true → c.b6 = false → c.b14 = false → c.b0 = false → f c = false
def Law334 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b6 = true → c.b16 = true → c.b8 = true → c.b9 = true → c.b15 = false → c.b10 = false → c.b12 = true → c.b11 = false → c.b0 = false → f c = true
def Law335 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b2 = true → c.b6 = true → c.b9 = false → c.b10 = false → c.b11 = true → c.b0 = false → c.b7 = true → c.b12 = true → f c = true
def Law336 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b10 = true → c.b8 = false → c.b4 = false → c.b16 = false → c.b0 = false → c.b1 = true → f c = false
def Law337 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b6 = false → c.b7 = true → c.b8 = true → c.b3 = false → c.b5 = true → c.b0 = false → c.b14 = false → c.b17 = false → c.b10 = true → c.b16 = false → c.b1 = true → c.b12 = true → c.b4 = false → c.b9 = false → f c = true
def Law338 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b4 = true → c.b6 = false → c.b0 = true → c.b8 = true → c.b15 = false → c.b5 = false → c.b14 = false → c.b7 = true → c.b1 = true → c.b12 = true → c.b16 = false → c.b3 = false → f c = false
def Law339 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b11 = false → c.b0 = true → c.b9 = false → c.b1 = true → c.b7 = true → c.b15 = true → c.b5 = true → c.b12 = false → c.b8 = false → c.b14 = false → c.b6 = false → c.b10 = true → c.b4 = false → f c = false
def Law340 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b5 = true → c.b14 = false → c.b1 = true → c.b10 = false → c.b0 = false → c.b4 = true → c.b6 = true → c.b15 = true → c.b9 = true → c.b8 = true → f c = false
def Law341 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b17 = true → c.b11 = true → c.b1 = true → c.b12 = true → c.b2 = true → c.b16 = true → c.b13 = false → c.b10 = false → c.b0 = false → c.b7 = false → c.b5 = true → c.b14 = false → c.b9 = true → c.b8 = true → c.b15 = false → f c = true
def Law342 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b1 = false → c.b4 = false → c.b14 = false → c.b3 = true → c.b16 = false → c.b9 = false → c.b11 = false → c.b13 = false → f c = true
def Law343 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b10 = true → c.b7 = false → c.b5 = false → c.b0 = false → c.b12 = true → c.b13 = true → c.b8 = false → c.b6 = false → c.b1 = true → c.b17 = true → c.b14 = true → f c = true
def Law344 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b9 = true → c.b6 = false → c.b13 = true → c.b8 = true → c.b17 = false → c.b14 = false → c.b3 = false → c.b16 = true → c.b11 = false → c.b15 = false → c.b7 = false → c.b0 = false → c.b2 = true → c.b12 = true → c.b4 = false → f c = true
def Law345 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b9 = true → c.b4 = false → c.b10 = false → c.b3 = false → c.b14 = false → c.b12 = true → c.b1 = true → c.b7 = false → c.b2 = true → c.b15 = false → c.b0 = false → c.b6 = false → c.b8 = true → c.b13 = false → c.b16 = true → c.b11 = false → f c = true
def Law346 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b8 = false → c.b7 = true → c.b0 = true → c.b6 = false → c.b2 = true → c.b14 = false → c.b15 = true → c.b4 = false → c.b11 = true → c.b10 = true → f c = true
def Law347 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b9 = true → c.b10 = true → c.b3 = false → c.b6 = true → c.b7 = true → c.b14 = false → c.b8 = true → c.b13 = false → c.b1 = true → c.b17 = true → c.b0 = true → f c = false
def Law348 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b7 = true → c.b1 = true → c.b6 = false → c.b16 = false → c.b13 = false → c.b11 = false → c.b15 = true → c.b14 = false → c.b12 = true → c.b0 = false → c.b3 = false → c.b17 = false → c.b10 = true → c.b5 = true → c.b8 = true → c.b4 = true → f c = true
def Law349 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b12 = true → c.b8 = true → c.b6 = true → c.b10 = false → c.b0 = false → c.b15 = true → c.b1 = true → c.b14 = false → c.b9 = false → c.b11 = false → f c = true
def Law350 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b12 = true → c.b4 = true → c.b17 = true → c.b5 = false → c.b10 = false → c.b2 = true → c.b13 = false → c.b0 = false → c.b14 = false → c.b1 = true → c.b7 = true → c.b15 = true → f c = false
def Law351 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b1 = true → c.b3 = false → c.b16 = true → c.b4 = false → c.b6 = false → c.b11 = true → c.b17 = false → c.b2 = true → c.b15 = false → c.b14 = false → c.b12 = true → c.b0 = false → c.b9 = true → c.b10 = true → c.b7 = false → f c = false
def Law352 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b13 = false → c.b10 = true → c.b7 = true → c.b4 = true → c.b8 = true → c.b17 = false → c.b0 = false → c.b12 = true → c.b1 = true → c.b3 = true → f c = true
def Law353 (f : Decide) : Prop := ∀ c : Case, c.b14 = true → c.b4 = true → c.b7 = false → c.b0 = false → c.b1 = true → c.b5 = false → c.b9 = true → c.b10 = false → c.b3 = false → c.b15 = true → c.b6 = true → c.b2 = false → c.b12 = true → f c = false
def Law354 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b1 = true → c.b17 = false → c.b0 = false → c.b4 = true → c.b15 = true → c.b12 = false → c.b2 = true → c.b8 = false → c.b13 = true → c.b10 = false → f c = true
def Law355 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b0 = false → c.b7 = true → c.b16 = false → c.b17 = false → c.b10 = true → c.b3 = false → c.b12 = true → c.b11 = false → c.b13 = false → c.b6 = false → c.b8 = false → c.b5 = false → c.b1 = true → f c = true
def Law356 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b5 = true → c.b16 = false → c.b4 = false → c.b15 = true → c.b11 = false → c.b12 = true → c.b14 = false → c.b1 = true → c.b7 = true → c.b6 = false → c.b0 = true → c.b10 = true → f c = true
def Law357 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b6 = false → c.b15 = true → c.b11 = true → c.b10 = false → c.b13 = false → c.b1 = true → c.b16 = true → c.b17 = true → c.b2 = true → c.b9 = true → c.b12 = true → c.b8 = true → c.b0 = false → c.b5 = true → c.b7 = false → f c = false
def Law358 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b0 = false → c.b10 = false → c.b11 = false → c.b6 = true → c.b8 = false → c.b12 = true → c.b15 = true → c.b13 = true → c.b9 = false → c.b14 = false → c.b3 = true → f c = false
def Law359 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b7 = false → c.b1 = false → c.b4 = false → c.b3 = false → c.b16 = true → c.b5 = false → f c = false
def Law360 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b10 = false → c.b1 = true → c.b9 = true → c.b8 = true → c.b2 = false → c.b14 = false → c.b0 = false → c.b12 = true → c.b16 = true → c.b17 = true → c.b7 = false → f c = true
def Law361 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b4 = false → c.b10 = false → c.b9 = true → c.b15 = false → c.b13 = true → c.b0 = false → c.b6 = true → c.b16 = false → c.b12 = false → c.b17 = true → f c = false
def Law362 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b13 = true → c.b6 = false → c.b10 = false → c.b5 = true → c.b7 = true → c.b15 = true → c.b1 = true → c.b17 = false → c.b2 = false → c.b11 = false → c.b9 = true → f c = false
def Law363 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b1 = true → c.b16 = false → c.b2 = false → c.b0 = false → c.b14 = false → c.b12 = true → c.b8 = false → c.b9 = true → c.b15 = false → c.b4 = false → c.b11 = true → c.b6 = true → f c = false
def Law364 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = true → c.b16 = false → c.b0 = true → c.b7 = false → c.b6 = false → c.b1 = true → c.b10 = false → c.b15 = true → c.b4 = false → f c = false
def Law365 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b13 = true → c.b0 = false → c.b1 = true → c.b17 = true → c.b15 = true → c.b12 = true → c.b5 = false → c.b4 = false → c.b6 = false → c.b7 = true → f c = true
def Law366 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b2 = false → c.b7 = true → c.b1 = true → c.b0 = true → c.b10 = true → c.b14 = false → c.b4 = false → c.b9 = true → c.b3 = false → c.b8 = false → f c = true
def Law367 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b16 = false → c.b3 = false → c.b12 = true → c.b7 = true → c.b4 = true → c.b6 = false → c.b14 = false → c.b0 = true → c.b15 = true → c.b2 = true → f c = false
def Law368 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b13 = false → c.b2 = true → c.b1 = true → c.b6 = false → c.b5 = false → c.b17 = true → c.b14 = false → c.b12 = true → c.b16 = true → c.b9 = false → c.b0 = false → c.b11 = true → c.b8 = true → c.b10 = true → f c = true
def Law369 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b17 = false → c.b16 = false → c.b4 = true → c.b12 = true → c.b3 = false → c.b5 = true → c.b7 = true → c.b10 = true → c.b15 = true → c.b14 = true → c.b13 = true → c.b6 = false → c.b1 = true → c.b8 = false → c.b11 = true → c.b9 = false → c.b0 = false → f c = true
def Law370 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b6 = false → c.b7 = true → c.b9 = false → c.b12 = true → c.b15 = false → c.b8 = true → c.b17 = false → c.b0 = false → c.b10 = true → c.b16 = true → c.b1 = true → c.b5 = false → c.b3 = false → f c = true
def Law371 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b3 = false → c.b5 = false → c.b4 = true → c.b14 = false → c.b12 = true → c.b15 = false → c.b6 = false → c.b7 = true → c.b16 = false → c.b13 = true → c.b1 = true → f c = true
def Law372 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b6 = true → c.b15 = true → c.b11 = false → c.b14 = false → c.b10 = false → c.b0 = false → c.b3 = false → c.b1 = true → c.b8 = false → c.b7 = true → c.b13 = true → c.b9 = false → f c = false
def Law373 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b13 = true → c.b0 = true → c.b12 = true → c.b7 = true → c.b14 = false → c.b1 = true → c.b2 = true → c.b8 = false → c.b10 = false → c.b6 = false → f c = false
def Law374 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b13 = false → c.b2 = true → c.b16 = true → c.b8 = true → c.b10 = false → c.b4 = false → c.b14 = false → c.b15 = true → c.b17 = false → c.b6 = false → c.b7 = false → c.b1 = true → f c = true
def Law375 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b11 = false → c.b10 = false → c.b6 = false → c.b14 = false → c.b1 = true → c.b8 = false → c.b0 = true → c.b2 = false → c.b7 = false → c.b16 = true → c.b9 = false → f c = false
def Law376 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b16 = false → c.b0 = false → c.b2 = false → c.b4 = true → c.b1 = true → c.b15 = false → c.b12 = false → c.b17 = true → c.b9 = true → c.b6 = true → f c = true
def Law377 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b1 = false → c.b16 = false → c.b7 = false → c.b12 = false → c.b0 = true → c.b3 = false → c.b9 = false → c.b6 = true → f c = false
def Law378 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b0 = false → c.b7 = false → c.b13 = false → c.b10 = true → c.b3 = false → c.b17 = true → c.b6 = false → c.b1 = true → c.b12 = true → c.b5 = false → c.b9 = false → c.b14 = true → f c = true
def Law379 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b13 = false → c.b3 = false → c.b9 = true → c.b4 = true → c.b1 = false → c.b16 = true → f c = true
def Law380 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b1 = true → c.b13 = false → c.b10 = true → c.b6 = true → c.b8 = true → c.b17 = false → c.b3 = false → c.b14 = false → c.b7 = true → c.b9 = true → f c = false
def Law381 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b6 = true → c.b15 = true → c.b10 = false → c.b12 = false → c.b17 = false → c.b2 = true → c.b0 = false → c.b1 = true → c.b13 = false → c.b14 = true → f c = true
def Law382 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b16 = true → c.b15 = true → c.b6 = false → c.b9 = false → c.b4 = true → c.b12 = true → c.b11 = false → c.b2 = false → c.b8 = true → c.b7 = false → c.b17 = true → c.b1 = true → c.b0 = false → c.b13 = false → f c = true
def Law383 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b1 = true → c.b5 = false → c.b12 = true → c.b15 = true → c.b10 = false → c.b0 = false → c.b6 = false → c.b7 = true → c.b8 = false → c.b17 = true → f c = true
def Law384 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b5 = true → c.b9 = true → c.b6 = true → c.b4 = true → c.b1 = true → c.b10 = false → c.b0 = false → c.b15 = false → c.b8 = true → c.b16 = false → c.b11 = false → f c = false
def Law385 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b12 = true → c.b10 = false → c.b2 = true → c.b4 = false → c.b15 = true → c.b17 = true → c.b8 = true → c.b5 = false → c.b1 = true → c.b14 = false → c.b7 = true → c.b0 = false → f c = true
def Law386 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b1 = true → c.b4 = false → c.b10 = false → c.b2 = false → c.b14 = false → c.b8 = false → c.b0 = true → c.b6 = false → f c = true
def Law387 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b13 = true → c.b1 = true → c.b10 = true → c.b6 = false → c.b17 = true → c.b16 = true → c.b2 = true → c.b3 = false → c.b15 = true → c.b5 = true → c.b12 = true → c.b4 = true → c.b8 = true → c.b14 = true → c.b0 = false → c.b11 = false → f c = false
def Law388 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b0 = false → c.b8 = false → c.b15 = false → c.b12 = true → c.b6 = false → c.b16 = true → c.b11 = true → c.b17 = false → c.b7 = true → c.b10 = false → f c = false
def Law389 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b5 = true → c.b11 = true → c.b16 = true → c.b14 = true → c.b4 = false → c.b10 = true → c.b6 = false → c.b1 = true → c.b3 = false → c.b7 = true → c.b17 = false → f c = true
def Law390 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b2 = false → c.b6 = false → c.b12 = true → c.b7 = false → c.b1 = true → c.b17 = false → c.b11 = true → c.b16 = true → c.b8 = true → c.b10 = false → c.b9 = true → c.b14 = false → f c = false
def Law391 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b7 = false → c.b9 = true → c.b16 = false → c.b3 = false → c.b1 = false → f c = true
def Law392 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b9 = false → c.b10 = true → c.b0 = false → c.b1 = true → c.b11 = true → c.b6 = false → c.b17 = false → c.b4 = false → c.b7 = true → c.b15 = true → c.b3 = false → c.b13 = true → c.b12 = true → c.b16 = false → f c = false
def Law393 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b14 = true → c.b0 = true → c.b6 = true → c.b10 = true → c.b2 = false → f c = false
def Law394 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b3 = false → c.b8 = false → c.b13 = true → c.b7 = true → c.b1 = true → c.b16 = false → c.b9 = true → c.b6 = false → c.b15 = false → c.b10 = true → c.b12 = true → c.b0 = false → c.b11 = false → c.b17 = false → f c = true
def Law395 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b9 = true → c.b2 = true → c.b5 = false → c.b7 = true → c.b6 = true → c.b14 = false → c.b0 = true → c.b10 = true → c.b8 = false → c.b16 = true → c.b17 = true → f c = true
def Law396 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b1 = false → c.b4 = true → c.b7 = false → c.b13 = true → c.b6 = false → c.b16 = false → f c = false
def Law397 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b7 = true → c.b14 = false → c.b1 = true → c.b5 = false → c.b3 = true → c.b16 = false → c.b2 = true → c.b17 = true → c.b6 = true → c.b0 = true → c.b9 = true → c.b8 = false → c.b10 = true → f c = true
def Law398 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b16 = true → c.b3 = false → c.b9 = false → c.b11 = true → c.b12 = false → c.b14 = false → c.b6 = true → c.b0 = true → c.b1 = true → f c = false
def Law399 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b14 = false → c.b0 = false → c.b2 = false → c.b17 = false → c.b1 = true → c.b16 = true → c.b5 = true → c.b12 = true → c.b7 = false → c.b8 = true → c.b9 = false → f c = true
def Law400 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b12 = false → c.b4 = true → c.b2 = false → c.b13 = true → c.b3 = true → c.b0 = false → c.b6 = true → c.b1 = true → c.b8 = false → c.b10 = false → c.b15 = true → f c = true
def Law401 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = true → c.b6 = false → c.b10 = true → c.b7 = false → c.b1 = true → c.b13 = true → f c = false
def Law402 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b2 = true → c.b5 = true → c.b14 = false → c.b1 = true → c.b0 = true → c.b4 = false → c.b7 = false → c.b10 = false → c.b6 = false → c.b16 = true → f c = true
def Law403 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b1 = true → c.b2 = true → c.b17 = true → c.b4 = true → c.b12 = true → c.b3 = false → c.b16 = false → c.b10 = false → c.b15 = true → c.b9 = true → c.b14 = true → c.b6 = true → c.b0 = false → f c = false
def Law404 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b10 = false → c.b14 = false → c.b0 = true → c.b7 = true → c.b1 = true → c.b6 = false → c.b2 = true → c.b8 = false → c.b4 = false → f c = true
def Law405 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = false → c.b3 = true → c.b1 = false → c.b5 = true → c.b11 = true → c.b7 = true → c.b4 = true → c.b16 = true → c.b8 = true → c.b0 = true → f c = true
def Law406 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b10 = false → c.b15 = false → c.b0 = false → c.b7 = false → c.b14 = true → c.b6 = true → c.b1 = true → c.b12 = false → f c = false
def Law407 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b6 = true → c.b2 = false → c.b3 = false → c.b5 = false → c.b7 = true → c.b14 = false → c.b13 = false → c.b4 = true → c.b17 = false → c.b1 = true → c.b15 = true → c.b12 = true → c.b8 = false → c.b9 = true → c.b10 = false → c.b0 = false → c.b11 = true → f c = true
def Law408 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b15 = true → c.b11 = false → c.b0 = true → c.b5 = false → c.b1 = true → c.b13 = false → c.b3 = true → c.b10 = true → c.b8 = false → c.b4 = false → c.b7 = true → c.b6 = false → f c = false
def Law409 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b17 = true → c.b5 = false → c.b13 = true → c.b1 = true → c.b14 = true → c.b7 = false → c.b10 = true → c.b12 = true → c.b8 = true → c.b0 = false → f c = false
def Law410 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b5 = true → c.b1 = true → c.b13 = true → c.b8 = true → c.b10 = true → c.b11 = false → c.b12 = true → c.b3 = false → c.b6 = false → c.b15 = true → c.b14 = false → c.b17 = false → c.b7 = true → c.b4 = true → c.b9 = false → c.b0 = false → f c = true
def Law411 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b10 = false → c.b8 = true → c.b11 = true → c.b17 = true → c.b1 = true → c.b0 = false → c.b2 = false → c.b3 = true → c.b9 = false → c.b5 = false → c.b7 = false → c.b15 = false → c.b14 = false → c.b16 = true → c.b6 = false → f c = false
def Law412 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b12 = false → c.b0 = false → c.b15 = true → c.b8 = true → c.b4 = true → c.b2 = false → c.b17 = false → c.b1 = true → c.b11 = true → c.b6 = true → c.b13 = true → f c = true
def Law413 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = false → c.b13 = true → c.b2 = false → c.b1 = true → c.b15 = true → c.b6 = false → c.b14 = false → c.b7 = false → c.b17 = true → c.b4 = true → c.b16 = true → c.b8 = true → c.b0 = false → f c = true
def Law414 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b7 = true → c.b14 = true → c.b15 = true → c.b3 = false → c.b2 = false → c.b10 = false → c.b1 = true → c.b5 = false → c.b9 = true → c.b12 = true → c.b0 = false → c.b4 = true → f c = false
def Law415 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b6 = true → c.b4 = false → c.b16 = true → c.b5 = true → c.b7 = false → c.b3 = false → c.b15 = false → f c = false
def Law416 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b2 = true → c.b10 = true → c.b5 = false → c.b8 = false → c.b16 = false → c.b17 = true → c.b7 = true → c.b6 = true → c.b3 = true → c.b0 = true → c.b11 = true → c.b9 = true → c.b14 = false → f c = true
def Law417 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b1 = true → c.b2 = true → c.b14 = false → c.b7 = true → c.b10 = false → c.b0 = true → c.b12 = false → c.b13 = true → c.b4 = false → c.b8 = false → f c = false
def Law418 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b0 = false → c.b1 = true → c.b10 = true → c.b16 = true → c.b6 = true → c.b3 = false → c.b4 = false → c.b13 = true → f c = false
def Law419 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b6 = false → c.b1 = true → c.b5 = true → c.b0 = false → c.b16 = true → c.b2 = true → c.b3 = true → c.b14 = false → c.b7 = false → c.b17 = true → c.b9 = false → c.b8 = true → c.b13 = false → c.b10 = false → c.b11 = true → f c = false
def Law420 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b0 = false → c.b14 = true → c.b12 = true → c.b1 = true → c.b7 = false → c.b10 = false → c.b3 = false → f c = false
def Law421 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b4 = true → c.b12 = true → c.b17 = true → c.b1 = true → c.b13 = false → c.b15 = true → c.b7 = true → c.b2 = true → c.b6 = false → c.b10 = false → c.b5 = false → c.b14 = true → c.b16 = false → f c = false
def Law422 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b4 = true → c.b7 = false → c.b8 = false → c.b16 = false → c.b1 = true → c.b6 = false → c.b5 = false → c.b0 = true → c.b10 = false → f c = false
def Law423 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b0 = false → c.b16 = true → c.b12 = true → c.b6 = false → c.b7 = false → c.b1 = true → c.b15 = true → c.b14 = false → c.b4 = true → f c = false
def Law424 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b9 = true → c.b17 = false → c.b12 = false → c.b1 = true → c.b15 = true → c.b0 = false → c.b6 = false → f c = true
def Law425 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b3 = false → c.b4 = true → c.b1 = false → c.b9 = true → c.b16 = true → c.b7 = false → c.b12 = false → f c = false
def Law426 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b14 = false → c.b13 = false → c.b7 = false → c.b12 = true → c.b0 = false → c.b1 = true → c.b16 = false → f c = false
def Law427 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b6 = false → c.b1 = false → c.b13 = true → c.b7 = false → c.b3 = false → c.b17 = false → c.b4 = false → f c = true
def Law428 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b6 = false → c.b14 = false → c.b0 = true → c.b2 = false → c.b16 = false → c.b1 = true → c.b4 = true → c.b3 = false → c.b15 = true → c.b12 = true → f c = false
def Law429 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b8 = false → c.b1 = true → c.b11 = false → c.b5 = true → c.b6 = false → c.b0 = true → c.b12 = true → c.b14 = false → c.b7 = true → c.b4 = false → c.b16 = true → c.b10 = true → f c = false
def Law430 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b14 = false → c.b12 = false → c.b13 = true → c.b10 = true → c.b4 = false → c.b0 = true → c.b6 = true → c.b9 = true → c.b11 = true → c.b8 = true → c.b16 = true → c.b1 = true → c.b3 = true → f c = false
def Law431 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b6 = false → c.b12 = true → c.b15 = true → c.b16 = false → c.b17 = false → c.b1 = true → c.b10 = true → c.b9 = false → c.b3 = false → c.b8 = true → c.b7 = true → c.b11 = false → c.b5 = false → c.b14 = false → f c = false
def Law432 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b2 = false → c.b10 = false → c.b0 = false → c.b1 = true → c.b17 = false → c.b11 = false → c.b8 = true → c.b6 = true → c.b13 = true → c.b15 = true → c.b4 = true → f c = false
def Law433 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b16 = true → c.b0 = false → c.b6 = false → c.b4 = true → c.b15 = true → c.b9 = false → c.b1 = true → c.b17 = false → f c = false
def Law434 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b4 = true → c.b10 = true → c.b0 = false → c.b7 = true → c.b3 = true → c.b1 = true → f c = true
def Law435 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b9 = false → c.b1 = false → c.b11 = false → c.b16 = false → c.b5 = true → c.b3 = true → c.b14 = false → f c = true
def Law436 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b9 = true → c.b0 = true → c.b10 = true → c.b14 = false → c.b8 = true → c.b1 = true → c.b6 = true → c.b7 = false → f c = true
def Law437 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b8 = false → c.b7 = true → c.b3 = false → f c = false
def Law438 (f : Decide) : Prop := ∀ c : Case, c.b17 = true → c.b15 = false → c.b10 = true → c.b16 = false → c.b9 = true → c.b11 = true → c.b14 = false → c.b1 = true → c.b8 = true → c.b4 = false → c.b7 = false → c.b12 = false → c.b6 = true → c.b0 = true → c.b13 = true → f c = true
def Law439 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b7 = true → c.b1 = true → c.b5 = true → c.b11 = true → c.b14 = true → c.b15 = false → c.b0 = false → c.b13 = true → c.b16 = true → c.b9 = true → c.b3 = false → c.b17 = true → c.b8 = false → c.b12 = true → c.b6 = false → c.b4 = true → c.b2 = true → f c = true
def Law440 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b10 = true → c.b3 = true → c.b1 = true → c.b6 = false → c.b13 = false → c.b17 = false → c.b0 = false → c.b8 = false → c.b7 = true → c.b4 = true → f c = true
def Law441 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b0 = false → c.b6 = false → c.b3 = true → c.b7 = false → c.b12 = true → c.b10 = true → c.b11 = false → c.b13 = true → c.b8 = true → c.b14 = false → c.b1 = true → c.b17 = true → c.b4 = true → c.b9 = false → c.b2 = true → c.b16 = true → f c = true
def Law442 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b6 = false → c.b0 = false → c.b16 = true → c.b14 = false → c.b12 = true → c.b7 = false → c.b1 = true → c.b8 = true → c.b4 = true → c.b2 = true → f c = true
def Law443 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b9 = true → c.b1 = true → c.b10 = false → c.b2 = true → c.b6 = false → c.b16 = true → c.b0 = true → c.b4 = false → f c = true
def Law444 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b16 = false → c.b14 = true → c.b11 = true → c.b2 = true → c.b3 = false → c.b15 = false → c.b5 = true → c.b7 = true → c.b17 = false → c.b6 = false → c.b0 = false → c.b1 = true → c.b9 = false → c.b12 = true → c.b10 = true → f c = true
def Law445 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b11 = false → c.b1 = false → c.b9 = false → c.b13 = false → c.b5 = true → c.b16 = false → c.b7 = false → c.b3 = true → f c = false
def Law446 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b2 = true → c.b1 = true → c.b0 = false → c.b4 = true → c.b13 = true → c.b7 = true → c.b5 = false → c.b17 = true → c.b6 = false → c.b11 = false → c.b10 = false → c.b12 = true → f c = false
def Law447 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b17 = true → c.b1 = true → c.b15 = true → c.b7 = true → c.b3 = false → c.b16 = true → c.b14 = true → c.b4 = false → c.b5 = true → c.b13 = true → c.b6 = false → c.b2 = true → c.b0 = false → c.b11 = false → f c = true
def Law448 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b16 = false → c.b6 = false → c.b1 = true → c.b17 = false → c.b7 = true → c.b11 = true → c.b10 = false → c.b2 = false → c.b12 = true → f c = false
def Law449 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b0 = false → c.b14 = false → c.b15 = false → c.b12 = true → c.b7 = false → c.b8 = false → c.b1 = true → c.b6 = false → c.b4 = true → f c = false
def Law450 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b12 = false → c.b0 = true → c.b1 = true → c.b14 = false → c.b10 = true → c.b9 = true → c.b6 = false → c.b8 = true → f c = true
def Law451 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b13 = true → c.b6 = false → c.b14 = false → c.b4 = true → c.b16 = true → c.b8 = true → c.b10 = true → c.b7 = false → c.b2 = true → c.b17 = true → c.b11 = true → c.b1 = true → c.b0 = false → f c = true
def Law452 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b15 = false → c.b11 = false → c.b9 = true → c.b12 = true → c.b6 = true → c.b0 = false → c.b8 = false → c.b1 = true → f c = false
def Law453 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b3 = false → c.b10 = true → c.b7 = true → c.b4 = true → c.b14 = false → c.b2 = true → c.b15 = false → c.b12 = false → c.b1 = true → c.b0 = true → c.b6 = false → f c = true
def Law454 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b4 = false → c.b12 = false → c.b17 = true → c.b11 = true → c.b0 = false → c.b1 = true → c.b16 = true → f c = true
def Law455 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b9 = false → c.b17 = true → c.b6 = true → c.b14 = false → c.b11 = false → c.b10 = true → c.b3 = false → c.b0 = true → f c = false
def Law456 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b7 = false → c.b1 = true → c.b4 = true → c.b12 = false → c.b2 = false → c.b10 = false → c.b14 = false → c.b17 = true → c.b0 = false → c.b16 = true → f c = true
def Law457 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b15 = true → c.b6 = false → c.b1 = true → c.b2 = false → c.b10 = false → c.b7 = false → c.b0 = true → c.b16 = false → c.b4 = false → f c = false
def Law458 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b6 = true → c.b1 = true → c.b5 = true → c.b0 = true → c.b10 = true → c.b14 = false → c.b7 = true → c.b9 = true → c.b8 = false → f c = false
def Law459 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b12 = true → c.b0 = false → c.b14 = true → c.b17 = false → c.b6 = false → c.b7 = false → c.b10 = true → f c = true
def Law460 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b12 = true → c.b3 = false → c.b11 = false → c.b16 = true → c.b9 = false → c.b1 = false → c.b7 = false → f c = false
def Law461 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b13 = true → c.b1 = true → c.b10 = true → c.b11 = false → c.b4 = true → c.b0 = true → c.b7 = true → c.b14 = false → c.b8 = true → c.b6 = true → f c = false
def Law462 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b14 = true → c.b5 = false → c.b16 = false → c.b3 = true → c.b1 = false → f c = false
def Law463 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b13 = true → c.b17 = true → c.b0 = false → c.b7 = false → c.b6 = false → c.b3 = true → c.b11 = false → c.b2 = true → c.b4 = false → c.b9 = false → c.b10 = true → c.b1 = true → c.b16 = true → c.b14 = false → c.b12 = true → c.b5 = true → f c = false
def Law464 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b6 = false → c.b13 = false → c.b1 = true → c.b17 = true → c.b5 = true → c.b12 = true → c.b0 = false → c.b14 = true → c.b15 = false → f c = true
def Law465 (f : Decide) : Prop := ∀ c : Case, c.b4 = true → c.b12 = false → c.b11 = true → c.b14 = true → c.b16 = true → c.b17 = true → c.b1 = true → c.b2 = false → c.b0 = false → c.b10 = false → c.b6 = true → f c = false
def Law466 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b5 = false → c.b14 = false → c.b15 = false → c.b7 = true → c.b16 = false → c.b1 = true → c.b3 = false → c.b13 = false → c.b12 = true → c.b2 = true → c.b6 = false → c.b4 = true → c.b0 = true → f c = true
def Law467 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b13 = true → c.b17 = false → c.b10 = false → c.b15 = true → c.b2 = true → c.b1 = true → c.b0 = false → c.b12 = false → c.b6 = true → c.b4 = false → f c = false
def Law468 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b1 = true → c.b4 = true → c.b3 = false → c.b7 = true → c.b6 = false → c.b14 = false → c.b0 = true → c.b12 = true → f c = false
def Law469 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b1 = false → c.b11 = true → c.b0 = true → c.b9 = false → c.b6 = true → c.b16 = false → c.b3 = false → c.b12 = false → f c = true
def Law470 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b3 = true → c.b10 = false → c.b9 = true → c.b0 = false → c.b2 = true → c.b4 = true → c.b6 = true → c.b15 = true → c.b1 = true → c.b14 = true → f c = true
def Law471 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b6 = true → c.b1 = true → c.b4 = true → c.b14 = false → c.b10 = true → c.b2 = false → c.b9 = true → c.b0 = true → c.b7 = true → f c = false
def Law472 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b6 = true → c.b13 = true → c.b11 = false → c.b7 = true → c.b12 = true → c.b8 = true → c.b1 = true → c.b14 = false → c.b3 = true → c.b0 = true → c.b10 = true → c.b4 = false → f c = false
def Law473 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b10 = false → c.b11 = true → c.b2 = false → c.b9 = false → c.b7 = true → c.b0 = false → c.b12 = true → c.b1 = true → f c = false
def Law474 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b16 = true → c.b7 = false → c.b12 = true → c.b10 = false → c.b1 = true → c.b17 = true → c.b6 = false → c.b3 = false → c.b0 = false → c.b11 = true → c.b5 = true → c.b14 = false → c.b9 = false → c.b8 = true → c.b13 = false → f c = true
def Law475 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b5 = true → c.b1 = false → c.b7 = false → c.b3 = false → c.b15 = true → c.b16 = true → f c = false
def Law476 (f : Decide) : Prop := ∀ c : Case, c.b17 = false → c.b8 = true → c.b12 = false → c.b13 = true → c.b11 = true → c.b1 = true → c.b9 = true → c.b0 = true → c.b10 = true → c.b4 = true → c.b6 = true → c.b14 = false → c.b7 = true → f c = true
def Law477 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = false → c.b7 = true → c.b17 = true → c.b1 = true → c.b10 = true → c.b16 = false → c.b6 = false → c.b15 = true → c.b13 = false → c.b5 = false → f c = true
def Law478 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b0 = true → c.b14 = true → c.b4 = true → c.b6 = false → c.b10 = false → c.b1 = true → f c = true
def Law479 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b1 = true → c.b14 = true → c.b11 = true → c.b2 = false → c.b6 = false → c.b12 = true → c.b10 = true → c.b4 = true → c.b15 = true → c.b0 = false → c.b13 = true → c.b5 = true → c.b8 = false → c.b16 = false → c.b3 = false → c.b9 = false → c.b17 = false → f c = false
def Law480 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b7 = true → c.b2 = true → c.b1 = true → c.b16 = false → c.b5 = false → c.b6 = false → c.b10 = true → c.b9 = false → c.b3 = false → c.b11 = true → c.b17 = false → c.b15 = false → c.b13 = true → c.b14 = true → c.b12 = true → f c = false
def Law481 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b11 = false → c.b12 = true → c.b6 = true → c.b7 = false → c.b0 = false → c.b13 = true → c.b15 = true → c.b10 = false → c.b9 = false → c.b14 = false → c.b3 = false → c.b8 = false → f c = true
def Law482 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b14 = false → c.b1 = true → c.b0 = false → c.b17 = false → c.b3 = false → c.b12 = false → c.b6 = true → c.b15 = false → f c = false
def Law483 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b7 = true → c.b2 = true → c.b17 = false → c.b0 = false → c.b8 = true → c.b12 = false → c.b6 = true → c.b15 = true → c.b13 = true → c.b1 = true → c.b9 = true → c.b4 = true → f c = true
def Law484 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b1 = true → c.b13 = false → c.b10 = true → c.b7 = false → c.b0 = true → c.b6 = false → f c = true
def Law485 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b4 = true → c.b14 = false → c.b12 = true → c.b1 = true → c.b8 = true → c.b7 = false → c.b17 = true → c.b11 = true → c.b9 = false → c.b15 = true → c.b0 = false → c.b2 = false → c.b13 = false → c.b6 = false → f c = false
def Law486 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b6 = true → c.b5 = false → c.b17 = false → c.b8 = true → c.b0 = false → c.b2 = true → c.b4 = true → c.b13 = true → c.b10 = false → c.b7 = false → c.b15 = true → c.b9 = true → c.b12 = false → f c = false
def Law487 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b1 = true → c.b4 = true → c.b14 = false → c.b10 = false → c.b8 = true → c.b9 = true → c.b15 = true → c.b0 = false → c.b12 = true → c.b5 = false → c.b6 = true → f c = false
def Law488 (f : Decide) : Prop := ∀ c : Case, c.b14 = false → c.b10 = false → c.b9 = true → c.b8 = false → c.b6 = true → c.b15 = true → c.b12 = true → c.b5 = true → c.b0 = false → c.b1 = true → c.b4 = true → f c = true
def Law489 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b8 = true → c.b13 = true → c.b14 = false → c.b16 = true → c.b11 = false → c.b2 = true → c.b17 = true → c.b10 = false → c.b1 = true → c.b7 = false → c.b6 = false → c.b12 = true → c.b9 = true → f c = true
def Law490 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b0 = false → c.b12 = true → c.b17 = true → c.b15 = false → c.b1 = true → c.b7 = true → c.b5 = false → f c = true
def Law491 (f : Decide) : Prop := ∀ c : Case, c.b16 = false → c.b11 = true → c.b0 = false → c.b2 = true → c.b15 = false → c.b12 = true → c.b6 = true → c.b1 = true → c.b9 = true → c.b13 = false → c.b8 = false → c.b10 = false → f c = false
def Law492 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b10 = false → c.b9 = true → c.b14 = false → c.b0 = false → c.b15 = true → c.b8 = false → c.b11 = false → c.b5 = false → c.b7 = false → c.b3 = false → c.b16 = true → c.b4 = true → c.b1 = true → c.b6 = true → f c = false
def Law493 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b3 = true → c.b0 = false → c.b7 = false → c.b14 = false → c.b5 = true → c.b1 = true → c.b8 = true → c.b6 = false → c.b12 = true → c.b17 = true → c.b9 = false → c.b2 = false → c.b15 = false → f c = true
def Law494 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b0 = false → c.b10 = false → c.b4 = false → c.b13 = true → c.b12 = false → c.b15 = true → c.b17 = false → c.b2 = true → c.b6 = true → c.b1 = true → f c = true
def Law495 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b0 = true → c.b16 = true → c.b7 = true → c.b4 = false → c.b14 = false → c.b1 = true → c.b8 = true → f c = false
def Law496 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b6 = false → c.b7 = false → c.b2 = true → c.b16 = true → c.b14 = false → c.b11 = false → c.b0 = false → c.b1 = true → c.b13 = false → c.b8 = true → c.b17 = true → c.b4 = false → f c = false
def Law497 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = true → c.b15 = true → c.b11 = true → c.b17 = true → c.b6 = true → c.b10 = false → c.b8 = false → c.b2 = false → c.b1 = true → c.b7 = true → c.b0 = false → c.b5 = false → c.b14 = false → c.b3 = false → c.b13 = false → c.b4 = true → c.b16 = true → f c = false
def Law498 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b2 = true → c.b6 = true → c.b1 = true → c.b4 = true → c.b17 = true → c.b10 = false → c.b12 = false → f c = false
def Law499 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = false → c.b6 = false → c.b1 = true → c.b11 = false → c.b0 = false → c.b17 = false → c.b7 = true → c.b15 = false → c.b16 = true → c.b2 = false → c.b10 = false → c.b13 = false → f c = false
def Law500 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b1 = true → c.b0 = true → c.b6 = true → f c = false
def Law501 (f : Decide) : Prop := ∀ c : Case, c.b15 = true → c.b9 = true → c.b1 = true → c.b6 = true → c.b7 = false → c.b16 = false → c.b10 = true → c.b11 = false → c.b0 = true → c.b8 = true → c.b14 = false → f c = false
def Law502 (f : Decide) : Prop := ∀ c : Case, c.b4 = false → c.b10 = false → c.b12 = true → c.b7 = false → c.b15 = false → c.b11 = true → c.b13 = true → c.b1 = true → c.b9 = true → c.b3 = false → c.b0 = false → c.b6 = true → c.b8 = true → f c = true
def Law503 (f : Decide) : Prop := ∀ c : Case, c.b16 = true → c.b17 = true → c.b13 = false → c.b0 = false → c.b5 = false → c.b12 = true → c.b3 = false → c.b14 = false → c.b1 = true → c.b2 = false → c.b4 = true → c.b9 = true → c.b11 = false → c.b7 = true → c.b8 = false → c.b6 = true → c.b10 = false → c.b15 = true → f c = true
def Law504 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b9 = true → c.b0 = false → c.b12 = true → c.b16 = true → c.b1 = true → c.b5 = true → c.b4 = true → c.b2 = false → c.b14 = true → c.b15 = true → c.b6 = true → c.b10 = false → f c = true
def Law505 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b1 = true → c.b9 = true → c.b8 = true → c.b7 = true → c.b10 = true → c.b12 = true → c.b4 = false → c.b13 = true → c.b0 = true → c.b6 = true → c.b14 = false → f c = false
def Law506 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b10 = true → c.b16 = false → c.b0 = true → c.b8 = true → c.b9 = true → c.b1 = true → c.b11 = true → c.b14 = false → c.b7 = false → c.b12 = true → c.b6 = true → c.b17 = false → f c = false
def Law507 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b12 = true → c.b4 = false → c.b1 = true → c.b7 = true → c.b2 = true → c.b14 = true → c.b3 = false → c.b17 = true → c.b10 = true → c.b16 = true → c.b6 = false → c.b5 = true → c.b13 = true → c.b0 = false → f c = true
def Law508 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b8 = true → c.b10 = false → c.b11 = true → c.b7 = true → c.b3 = false → c.b9 = true → c.b1 = true → c.b0 = false → c.b15 = false → c.b17 = true → c.b6 = true → f c = false
def Law509 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b13 = true → c.b14 = false → c.b17 = true → c.b0 = true → c.b9 = true → c.b6 = true → c.b15 = true → c.b16 = false → c.b11 = true → c.b1 = true → c.b7 = false → c.b10 = true → c.b12 = false → f c = false
def Law510 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b11 = false → c.b5 = false → c.b9 = false → c.b16 = false → c.b4 = false → c.b13 = true → c.b1 = false → c.b14 = false → f c = false
def Law511 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b3 = false → c.b12 = false → c.b4 = false → c.b14 = false → c.b9 = true → c.b7 = false → c.b1 = true → c.b10 = true → c.b0 = true → c.b6 = true → c.b8 = false → f c = false

def Group0 (f : Decide) : Prop :=
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
  Law15 f

def Group1 (f : Decide) : Prop :=
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

def Group2 (f : Decide) : Prop :=
  Law32 f ∧
  Law33 f ∧
  Law34 f ∧
  Law35 f ∧
  Law36 f ∧
  Law37 f ∧
  Law38 f ∧
  Law39 f ∧
  Law40 f ∧
  Law41 f ∧
  Law42 f ∧
  Law43 f ∧
  Law44 f ∧
  Law45 f ∧
  Law46 f ∧
  Law47 f

def Group3 (f : Decide) : Prop :=
  Law48 f ∧
  Law49 f ∧
  Law50 f ∧
  Law51 f ∧
  Law52 f ∧
  Law53 f ∧
  Law54 f ∧
  Law55 f ∧
  Law56 f ∧
  Law57 f ∧
  Law58 f ∧
  Law59 f ∧
  Law60 f ∧
  Law61 f ∧
  Law62 f ∧
  Law63 f

def Group4 (f : Decide) : Prop :=
  Law64 f ∧
  Law65 f ∧
  Law66 f ∧
  Law67 f ∧
  Law68 f ∧
  Law69 f ∧
  Law70 f ∧
  Law71 f ∧
  Law72 f ∧
  Law73 f ∧
  Law74 f ∧
  Law75 f ∧
  Law76 f ∧
  Law77 f ∧
  Law78 f ∧
  Law79 f

def Group5 (f : Decide) : Prop :=
  Law80 f ∧
  Law81 f ∧
  Law82 f ∧
  Law83 f ∧
  Law84 f ∧
  Law85 f ∧
  Law86 f ∧
  Law87 f ∧
  Law88 f ∧
  Law89 f ∧
  Law90 f ∧
  Law91 f ∧
  Law92 f ∧
  Law93 f ∧
  Law94 f ∧
  Law95 f

def Group6 (f : Decide) : Prop :=
  Law96 f ∧
  Law97 f ∧
  Law98 f ∧
  Law99 f ∧
  Law100 f ∧
  Law101 f ∧
  Law102 f ∧
  Law103 f ∧
  Law104 f ∧
  Law105 f ∧
  Law106 f ∧
  Law107 f ∧
  Law108 f ∧
  Law109 f ∧
  Law110 f ∧
  Law111 f

def Group7 (f : Decide) : Prop :=
  Law112 f ∧
  Law113 f ∧
  Law114 f ∧
  Law115 f ∧
  Law116 f ∧
  Law117 f ∧
  Law118 f ∧
  Law119 f ∧
  Law120 f ∧
  Law121 f ∧
  Law122 f ∧
  Law123 f ∧
  Law124 f ∧
  Law125 f ∧
  Law126 f ∧
  Law127 f

def Group8 (f : Decide) : Prop :=
  Law128 f ∧
  Law129 f ∧
  Law130 f ∧
  Law131 f ∧
  Law132 f ∧
  Law133 f ∧
  Law134 f ∧
  Law135 f ∧
  Law136 f ∧
  Law137 f ∧
  Law138 f ∧
  Law139 f ∧
  Law140 f ∧
  Law141 f ∧
  Law142 f ∧
  Law143 f

def Group9 (f : Decide) : Prop :=
  Law144 f ∧
  Law145 f ∧
  Law146 f ∧
  Law147 f ∧
  Law148 f ∧
  Law149 f ∧
  Law150 f ∧
  Law151 f ∧
  Law152 f ∧
  Law153 f ∧
  Law154 f ∧
  Law155 f ∧
  Law156 f ∧
  Law157 f ∧
  Law158 f ∧
  Law159 f

def Group10 (f : Decide) : Prop :=
  Law160 f ∧
  Law161 f ∧
  Law162 f ∧
  Law163 f ∧
  Law164 f ∧
  Law165 f ∧
  Law166 f ∧
  Law167 f ∧
  Law168 f ∧
  Law169 f ∧
  Law170 f ∧
  Law171 f ∧
  Law172 f ∧
  Law173 f ∧
  Law174 f ∧
  Law175 f

def Group11 (f : Decide) : Prop :=
  Law176 f ∧
  Law177 f ∧
  Law178 f ∧
  Law179 f ∧
  Law180 f ∧
  Law181 f ∧
  Law182 f ∧
  Law183 f ∧
  Law184 f ∧
  Law185 f ∧
  Law186 f ∧
  Law187 f ∧
  Law188 f ∧
  Law189 f ∧
  Law190 f ∧
  Law191 f

def Group12 (f : Decide) : Prop :=
  Law192 f ∧
  Law193 f ∧
  Law194 f ∧
  Law195 f ∧
  Law196 f ∧
  Law197 f ∧
  Law198 f ∧
  Law199 f ∧
  Law200 f ∧
  Law201 f ∧
  Law202 f ∧
  Law203 f ∧
  Law204 f ∧
  Law205 f ∧
  Law206 f ∧
  Law207 f

def Group13 (f : Decide) : Prop :=
  Law208 f ∧
  Law209 f ∧
  Law210 f ∧
  Law211 f ∧
  Law212 f ∧
  Law213 f ∧
  Law214 f ∧
  Law215 f ∧
  Law216 f ∧
  Law217 f ∧
  Law218 f ∧
  Law219 f ∧
  Law220 f ∧
  Law221 f ∧
  Law222 f ∧
  Law223 f

def Group14 (f : Decide) : Prop :=
  Law224 f ∧
  Law225 f ∧
  Law226 f ∧
  Law227 f ∧
  Law228 f ∧
  Law229 f ∧
  Law230 f ∧
  Law231 f ∧
  Law232 f ∧
  Law233 f ∧
  Law234 f ∧
  Law235 f ∧
  Law236 f ∧
  Law237 f ∧
  Law238 f ∧
  Law239 f

def Group15 (f : Decide) : Prop :=
  Law240 f ∧
  Law241 f ∧
  Law242 f ∧
  Law243 f ∧
  Law244 f ∧
  Law245 f ∧
  Law246 f ∧
  Law247 f ∧
  Law248 f ∧
  Law249 f ∧
  Law250 f ∧
  Law251 f ∧
  Law252 f ∧
  Law253 f ∧
  Law254 f ∧
  Law255 f

def Group16 (f : Decide) : Prop :=
  Law256 f ∧
  Law257 f ∧
  Law258 f ∧
  Law259 f ∧
  Law260 f ∧
  Law261 f ∧
  Law262 f ∧
  Law263 f ∧
  Law264 f ∧
  Law265 f ∧
  Law266 f ∧
  Law267 f ∧
  Law268 f ∧
  Law269 f ∧
  Law270 f ∧
  Law271 f

def Group17 (f : Decide) : Prop :=
  Law272 f ∧
  Law273 f ∧
  Law274 f ∧
  Law275 f ∧
  Law276 f ∧
  Law277 f ∧
  Law278 f ∧
  Law279 f ∧
  Law280 f ∧
  Law281 f ∧
  Law282 f ∧
  Law283 f ∧
  Law284 f ∧
  Law285 f ∧
  Law286 f ∧
  Law287 f

def Group18 (f : Decide) : Prop :=
  Law288 f ∧
  Law289 f ∧
  Law290 f ∧
  Law291 f ∧
  Law292 f ∧
  Law293 f ∧
  Law294 f ∧
  Law295 f ∧
  Law296 f ∧
  Law297 f ∧
  Law298 f ∧
  Law299 f ∧
  Law300 f ∧
  Law301 f ∧
  Law302 f ∧
  Law303 f

def Group19 (f : Decide) : Prop :=
  Law304 f ∧
  Law305 f ∧
  Law306 f ∧
  Law307 f ∧
  Law308 f ∧
  Law309 f ∧
  Law310 f ∧
  Law311 f ∧
  Law312 f ∧
  Law313 f ∧
  Law314 f ∧
  Law315 f ∧
  Law316 f ∧
  Law317 f ∧
  Law318 f ∧
  Law319 f

def Group20 (f : Decide) : Prop :=
  Law320 f ∧
  Law321 f ∧
  Law322 f ∧
  Law323 f ∧
  Law324 f ∧
  Law325 f ∧
  Law326 f ∧
  Law327 f ∧
  Law328 f ∧
  Law329 f ∧
  Law330 f ∧
  Law331 f ∧
  Law332 f ∧
  Law333 f ∧
  Law334 f ∧
  Law335 f

def Group21 (f : Decide) : Prop :=
  Law336 f ∧
  Law337 f ∧
  Law338 f ∧
  Law339 f ∧
  Law340 f ∧
  Law341 f ∧
  Law342 f ∧
  Law343 f ∧
  Law344 f ∧
  Law345 f ∧
  Law346 f ∧
  Law347 f ∧
  Law348 f ∧
  Law349 f ∧
  Law350 f ∧
  Law351 f

def Group22 (f : Decide) : Prop :=
  Law352 f ∧
  Law353 f ∧
  Law354 f ∧
  Law355 f ∧
  Law356 f ∧
  Law357 f ∧
  Law358 f ∧
  Law359 f ∧
  Law360 f ∧
  Law361 f ∧
  Law362 f ∧
  Law363 f ∧
  Law364 f ∧
  Law365 f ∧
  Law366 f ∧
  Law367 f

def Group23 (f : Decide) : Prop :=
  Law368 f ∧
  Law369 f ∧
  Law370 f ∧
  Law371 f ∧
  Law372 f ∧
  Law373 f ∧
  Law374 f ∧
  Law375 f ∧
  Law376 f ∧
  Law377 f ∧
  Law378 f ∧
  Law379 f ∧
  Law380 f ∧
  Law381 f ∧
  Law382 f ∧
  Law383 f

def Group24 (f : Decide) : Prop :=
  Law384 f ∧
  Law385 f ∧
  Law386 f ∧
  Law387 f ∧
  Law388 f ∧
  Law389 f ∧
  Law390 f ∧
  Law391 f ∧
  Law392 f ∧
  Law393 f ∧
  Law394 f ∧
  Law395 f ∧
  Law396 f ∧
  Law397 f ∧
  Law398 f ∧
  Law399 f

def Group25 (f : Decide) : Prop :=
  Law400 f ∧
  Law401 f ∧
  Law402 f ∧
  Law403 f ∧
  Law404 f ∧
  Law405 f ∧
  Law406 f ∧
  Law407 f ∧
  Law408 f ∧
  Law409 f ∧
  Law410 f ∧
  Law411 f ∧
  Law412 f ∧
  Law413 f ∧
  Law414 f ∧
  Law415 f

def Group26 (f : Decide) : Prop :=
  Law416 f ∧
  Law417 f ∧
  Law418 f ∧
  Law419 f ∧
  Law420 f ∧
  Law421 f ∧
  Law422 f ∧
  Law423 f ∧
  Law424 f ∧
  Law425 f ∧
  Law426 f ∧
  Law427 f ∧
  Law428 f ∧
  Law429 f ∧
  Law430 f ∧
  Law431 f

def Group27 (f : Decide) : Prop :=
  Law432 f ∧
  Law433 f ∧
  Law434 f ∧
  Law435 f ∧
  Law436 f ∧
  Law437 f ∧
  Law438 f ∧
  Law439 f ∧
  Law440 f ∧
  Law441 f ∧
  Law442 f ∧
  Law443 f ∧
  Law444 f ∧
  Law445 f ∧
  Law446 f ∧
  Law447 f

def Group28 (f : Decide) : Prop :=
  Law448 f ∧
  Law449 f ∧
  Law450 f ∧
  Law451 f ∧
  Law452 f ∧
  Law453 f ∧
  Law454 f ∧
  Law455 f ∧
  Law456 f ∧
  Law457 f ∧
  Law458 f ∧
  Law459 f ∧
  Law460 f ∧
  Law461 f ∧
  Law462 f ∧
  Law463 f

def Group29 (f : Decide) : Prop :=
  Law464 f ∧
  Law465 f ∧
  Law466 f ∧
  Law467 f ∧
  Law468 f ∧
  Law469 f ∧
  Law470 f ∧
  Law471 f ∧
  Law472 f ∧
  Law473 f ∧
  Law474 f ∧
  Law475 f ∧
  Law476 f ∧
  Law477 f ∧
  Law478 f ∧
  Law479 f

def Group30 (f : Decide) : Prop :=
  Law480 f ∧
  Law481 f ∧
  Law482 f ∧
  Law483 f ∧
  Law484 f ∧
  Law485 f ∧
  Law486 f ∧
  Law487 f ∧
  Law488 f ∧
  Law489 f ∧
  Law490 f ∧
  Law491 f ∧
  Law492 f ∧
  Law493 f ∧
  Law494 f ∧
  Law495 f

def Group31 (f : Decide) : Prop :=
  Law496 f ∧
  Law497 f ∧
  Law498 f ∧
  Law499 f ∧
  Law500 f ∧
  Law501 f ∧
  Law502 f ∧
  Law503 f ∧
  Law504 f ∧
  Law505 f ∧
  Law506 f ∧
  Law507 f ∧
  Law508 f ∧
  Law509 f ∧
  Law510 f ∧
  Law511 f

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
