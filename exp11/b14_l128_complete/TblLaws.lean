/-
Hard Proof, experiment 11. GENERATED FILE (human-owned). The laws: one for each leaf of the rule.
-/
import Tbl

namespace Tbl

def Law0 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b6 = false → c.b1 = false → c.b0 = true → c.b4 = false → c.b2 = true → c.b5 = false → c.b3 = false → c.b10 = false → c.b13 = false → c.b9 = false → c.b7 = false → c.b8 = true → c.b11 = true → f c = true
def Law1 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b11 = false → c.b5 = true → c.b6 = true → c.b13 = false → c.b4 = false → c.b0 = true → c.b9 = true → c.b10 = true → c.b8 = true → c.b2 = true → f c = false
def Law2 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b10 = false → c.b9 = false → c.b0 = true → c.b6 = false → c.b7 = true → c.b8 = true → c.b4 = false → c.b13 = false → f c = false
def Law3 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b9 = false → c.b4 = true → c.b13 = false → c.b5 = false → c.b10 = false → c.b8 = true → c.b11 = false → c.b6 = false → f c = true
def Law4 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b0 = true → c.b13 = false → c.b7 = true → c.b1 = true → c.b11 = false → c.b8 = false → c.b5 = true → c.b12 = true → c.b4 = false → f c = false
def Law5 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b5 = false → c.b9 = true → c.b12 = false → c.b0 = true → c.b13 = false → c.b4 = true → f c = true
def Law6 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b8 = false → c.b6 = false → c.b7 = true → c.b3 = true → c.b9 = false → c.b10 = false → c.b0 = true → c.b13 = false → f c = true
def Law7 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b9 = true → c.b5 = true → c.b12 = false → c.b4 = true → c.b8 = false → c.b13 = false → f c = true
def Law8 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b9 = false → c.b3 = false → c.b4 = true → c.b13 = false → c.b6 = false → c.b10 = false → c.b11 = true → c.b5 = false → f c = false
def Law9 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b9 = true → c.b3 = true → c.b13 = false → c.b6 = false → c.b2 = true → c.b8 = true → c.b10 = false → c.b11 = true → c.b5 = true → c.b7 = false → f c = true
def Law10 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b12 = false → c.b0 = true → c.b9 = true → c.b5 = false → c.b2 = true → c.b13 = false → f c = true
def Law11 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b5 = true → c.b2 = true → c.b1 = true → c.b13 = false → c.b6 = true → f c = true
def Law12 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b4 = false → c.b0 = true → c.b9 = true → c.b5 = false → c.b13 = false → c.b2 = true → c.b3 = true → c.b12 = false → f c = true
def Law13 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b10 = false → c.b6 = false → c.b3 = false → c.b5 = true → c.b9 = false → c.b1 = false → c.b4 = true → c.b13 = false → c.b7 = true → c.b2 = false → c.b0 = true → f c = false
def Law14 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b11 = true → c.b10 = false → c.b9 = true → c.b0 = true → c.b8 = true → c.b7 = false → c.b6 = false → c.b3 = false → c.b13 = false → c.b2 = true → f c = false
def Law15 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b7 = true → c.b13 = false → c.b9 = true → c.b5 = true → c.b12 = false → c.b0 = true → c.b11 = false → c.b3 = true → c.b6 = true → c.b1 = false → c.b4 = false → f c = false
def Law16 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b13 = false → c.b9 = true → c.b5 = true → c.b1 = false → c.b7 = true → c.b8 = false → c.b4 = false → c.b11 = false → c.b0 = true → f c = false
def Law17 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b5 = true → c.b13 = false → c.b3 = true → c.b11 = true → c.b4 = false → c.b0 = true → c.b1 = false → c.b9 = true → f c = false
def Law18 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b11 = false → c.b9 = true → c.b2 = true → c.b0 = true → c.b1 = true → c.b3 = false → c.b12 = true → c.b4 = true → c.b6 = false → c.b8 = true → c.b10 = true → c.b5 = true → c.b13 = false → f c = false
def Law19 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b11 = true → c.b5 = true → c.b13 = false → c.b3 = false → c.b0 = true → c.b6 = false → c.b2 = true → c.b9 = false → f c = true
def Law20 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b11 = false → c.b0 = true → c.b7 = false → c.b2 = true → c.b10 = true → c.b6 = false → c.b12 = true → c.b8 = true → c.b9 = true → c.b5 = true → c.b4 = true → c.b3 = true → c.b1 = false → f c = false
def Law21 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b10 = false → c.b5 = false → c.b11 = true → c.b6 = false → c.b0 = true → c.b3 = false → c.b12 = false → c.b9 = false → c.b4 = false → c.b13 = false → f c = true
def Law22 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b2 = false → c.b13 = false → c.b8 = false → c.b10 = false → c.b4 = false → c.b3 = false → c.b6 = false → c.b5 = true → c.b7 = true → c.b0 = true → c.b9 = false → c.b12 = true → c.b11 = true → f c = true
def Law23 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b0 = true → c.b5 = true → c.b13 = false → c.b6 = false → c.b11 = true → c.b1 = true → c.b10 = false → c.b4 = true → c.b7 = true → c.b9 = false → c.b8 = true → c.b3 = false → c.b2 = false → f c = true
def Law24 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b8 = true → c.b1 = true → c.b5 = true → c.b11 = true → c.b10 = false → c.b13 = false → c.b6 = true → c.b9 = true → c.b0 = true → c.b2 = true → f c = true
def Law25 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b0 = true → c.b10 = false → c.b5 = false → c.b12 = true → c.b6 = false → c.b13 = false → c.b3 = false → c.b4 = false → c.b2 = false → c.b9 = false → f c = false
def Law26 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b1 = false → c.b4 = false → c.b10 = true → c.b5 = true → c.b11 = true → c.b8 = true → c.b0 = true → c.b7 = false → c.b2 = true → c.b9 = true → f c = false
def Law27 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b0 = true → c.b10 = false → c.b12 = false → c.b6 = false → c.b9 = false → c.b7 = false → c.b3 = false → c.b1 = true → c.b13 = false → c.b5 = false → c.b11 = true → c.b4 = false → f c = false
def Law28 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b6 = false → c.b8 = true → c.b11 = false → c.b9 = true → c.b7 = true → c.b5 = true → c.b10 = true → c.b12 = false → c.b2 = true → c.b4 = true → c.b0 = true → f c = false
def Law29 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b2 = true → c.b6 = false → c.b1 = true → c.b13 = false → c.b5 = true → f c = true
def Law30 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b0 = true → c.b6 = false → c.b12 = true → c.b13 = false → c.b7 = false → c.b8 = true → c.b9 = false → c.b4 = true → c.b10 = false → c.b5 = true → c.b3 = false → c.b2 = false → f c = false
def Law31 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b11 = true → c.b13 = false → c.b1 = true → c.b7 = true → c.b0 = true → c.b5 = true → c.b10 = false → c.b3 = false → c.b4 = true → c.b6 = false → c.b2 = false → c.b9 = false → c.b8 = false → f c = false
def Law32 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b7 = false → c.b6 = true → c.b3 = false → c.b10 = false → c.b13 = false → c.b0 = true → c.b12 = false → c.b9 = false → f c = false
def Law33 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b0 = true → c.b9 = false → c.b13 = false → c.b8 = false → c.b4 = false → c.b2 = false → c.b11 = true → c.b10 = false → c.b3 = false → c.b5 = true → c.b1 = true → c.b12 = false → c.b6 = false → f c = false
def Law34 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b7 = false → c.b2 = true → c.b13 = false → c.b11 = false → c.b6 = false → c.b12 = false → c.b0 = true → c.b8 = true → c.b4 = true → c.b9 = true → c.b10 = true → f c = false
def Law35 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b3 = false → c.b8 = true → c.b13 = false → c.b7 = true → c.b4 = true → c.b12 = false → c.b6 = false → c.b1 = true → c.b9 = false → c.b2 = false → c.b10 = false → c.b5 = true → c.b0 = true → f c = true
def Law36 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b2 = true → c.b8 = true → c.b6 = true → c.b7 = false → c.b5 = true → c.b0 = true → c.b11 = true → c.b10 = false → c.b9 = true → f c = true
def Law37 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b9 = false → c.b3 = false → c.b11 = true → c.b0 = true → c.b7 = false → c.b5 = true → c.b12 = false → c.b13 = false → c.b4 = true → c.b10 = false → c.b6 = false → f c = true
def Law38 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b10 = true → c.b4 = true → c.b8 = true → c.b2 = true → c.b0 = true → c.b6 = false → c.b7 = true → c.b9 = true → c.b11 = false → c.b13 = false → c.b1 = true → c.b5 = true → c.b12 = true → f c = false
def Law39 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b13 = true → c.b5 = false → c.b12 = false → f c = true
def Law40 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b8 = false → c.b1 = true → c.b9 = true → c.b3 = false → c.b13 = false → c.b0 = true → c.b4 = false → c.b5 = true → f c = false
def Law41 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b2 = false → c.b5 = false → c.b3 = true → c.b12 = false → c.b7 = true → c.b4 = false → c.b13 = false → c.b1 = false → c.b8 = false → c.b0 = true → f c = false
def Law42 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b2 = true → c.b1 = true → c.b13 = false → c.b0 = false → f c = true
def Law43 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b3 = false → c.b6 = true → c.b7 = true → c.b0 = true → c.b13 = false → c.b11 = true → c.b9 = false → f c = true
def Law44 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b5 = false → c.b8 = false → c.b12 = false → f c = true
def Law45 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b0 = true → c.b1 = true → c.b4 = false → c.b11 = true → c.b5 = true → c.b13 = false → c.b3 = true → c.b9 = true → f c = true
def Law46 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b10 = false → c.b0 = true → c.b3 = false → c.b6 = false → c.b4 = false → c.b2 = false → c.b7 = false → c.b9 = false → c.b5 = true → c.b11 = true → f c = true
def Law47 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b3 = false → c.b11 = false → c.b8 = false → c.b0 = true → c.b10 = false → c.b6 = false → c.b13 = false → c.b9 = false → f c = false
def Law48 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b0 = true → c.b12 = false → c.b13 = false → c.b2 = false → c.b5 = false → c.b3 = true → c.b8 = true → c.b4 = false → c.b7 = true → c.b9 = true → f c = true
def Law49 (f : Decide) : Prop := ∀ c : Case, c.b12 = true → c.b9 = true → c.b5 = true → c.b0 = true → c.b8 = false → c.b4 = true → c.b13 = false → f c = false
def Law50 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b13 = false → c.b8 = true → c.b0 = true → c.b3 = true → c.b11 = false → c.b5 = true → c.b10 = false → c.b2 = true → f c = true
def Law51 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b6 = true → c.b10 = true → c.b11 = false → c.b9 = true → c.b8 = true → c.b2 = true → c.b5 = true → c.b0 = true → c.b4 = true → f c = true
def Law52 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b10 = false → c.b0 = true → c.b9 = false → c.b3 = true → c.b4 = true → c.b13 = false → c.b5 = true → f c = true
def Law53 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b13 = false → c.b5 = true → c.b11 = false → c.b12 = true → c.b7 = false → c.b9 = true → c.b4 = true → c.b10 = true → c.b3 = false → c.b8 = true → c.b0 = true → c.b1 = true → c.b6 = false → f c = true
def Law54 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b2 = false → c.b13 = false → c.b4 = false → c.b5 = true → c.b0 = false → f c = false
def Law55 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b1 = true → c.b9 = true → c.b0 = true → c.b5 = false → c.b2 = false → c.b13 = false → f c = true
def Law56 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b2 = false → c.b4 = false → c.b0 = false → c.b13 = false → f c = false
def Law57 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b3 = false → c.b11 = true → c.b10 = false → c.b1 = false → c.b2 = false → c.b4 = false → c.b6 = false → c.b9 = false → c.b0 = true → c.b13 = false → c.b7 = true → f c = true
def Law58 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b4 = false → c.b0 = true → c.b1 = false → c.b7 = false → c.b5 = false → c.b13 = false → c.b3 = false → c.b10 = false → c.b8 = false → c.b12 = false → c.b9 = true → f c = false
def Law59 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b13 = true → f c = true
def Law60 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b9 = false → c.b13 = false → c.b10 = false → c.b4 = false → c.b6 = false → c.b11 = false → c.b7 = false → c.b0 = true → f c = false
def Law61 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b0 = true → c.b11 = true → c.b9 = false → c.b10 = true → c.b3 = false → f c = true
def Law62 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b6 = false → c.b10 = false → c.b2 = false → c.b5 = true → c.b12 = false → c.b3 = false → c.b9 = false → c.b0 = true → c.b1 = true → c.b7 = true → c.b4 = false → c.b13 = false → c.b11 = true → f c = false
def Law63 (f : Decide) : Prop := ∀ c : Case, c.b11 = false → c.b6 = false → c.b13 = false → c.b5 = true → c.b9 = false → c.b3 = false → c.b10 = false → c.b8 = false → c.b7 = false → c.b0 = true → f c = false
def Law64 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b13 = false → c.b5 = true → c.b7 = false → c.b4 = false → c.b11 = false → c.b9 = true → c.b0 = true → f c = false
def Law65 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b13 = false → c.b0 = false → c.b1 = false → c.b2 = true → c.b9 = true → f c = false
def Law66 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b0 = false → c.b13 = false → c.b11 = true → c.b4 = true → f c = false
def Law67 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b4 = false → c.b9 = true → c.b7 = false → c.b2 = false → c.b3 = false → c.b5 = false → c.b1 = false → c.b12 = false → c.b13 = false → f c = true
def Law68 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b6 = true → c.b10 = false → c.b13 = false → c.b11 = true → c.b7 = false → c.b3 = false → c.b0 = true → c.b5 = false → c.b12 = true → f c = false
def Law69 (f : Decide) : Prop := ∀ c : Case, c.b6 = false → c.b10 = false → c.b1 = false → c.b13 = false → c.b7 = false → c.b8 = false → c.b9 = false → c.b5 = false → c.b0 = true → c.b3 = false → c.b12 = false → c.b11 = true → c.b2 = true → c.b4 = false → f c = true
def Law70 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b0 = true → c.b4 = true → c.b11 = false → c.b9 = false → c.b5 = true → c.b10 = false → c.b6 = false → c.b13 = false → f c = true
def Law71 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b0 = true → c.b1 = false → c.b5 = false → c.b12 = false → c.b8 = true → c.b10 = false → c.b2 = true → c.b3 = false → c.b9 = true → c.b13 = false → c.b4 = false → f c = true
def Law72 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b13 = false → c.b4 = true → c.b8 = true → c.b11 = true → c.b0 = true → c.b1 = false → c.b7 = false → c.b9 = true → c.b2 = true → c.b5 = true → f c = true
def Law73 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b13 = true → c.b12 = true → c.b5 = false → f c = true
def Law74 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b0 = true → c.b10 = false → c.b13 = false → c.b11 = true → c.b3 = true → c.b9 = false → f c = false
def Law75 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b9 = false → c.b13 = false → c.b3 = true → c.b0 = true → f c = false
def Law76 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b7 = false → c.b13 = false → c.b9 = false → c.b3 = false → c.b11 = true → c.b6 = false → c.b4 = true → c.b8 = false → c.b12 = true → c.b10 = false → c.b5 = true → c.b0 = true → f c = true
def Law77 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b13 = false → c.b9 = false → c.b10 = false → c.b6 = false → c.b3 = true → c.b8 = false → c.b0 = true → c.b11 = false → f c = true
def Law78 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b12 = false → c.b5 = false → c.b7 = true → c.b3 = false → c.b11 = false → c.b4 = false → c.b9 = true → c.b1 = false → c.b0 = true → c.b2 = true → f c = true
def Law79 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b9 = true → c.b5 = true → c.b13 = false → c.b7 = true → c.b12 = false → c.b3 = false → c.b10 = true → c.b6 = false → c.b11 = false → c.b8 = true → c.b2 = true → c.b4 = false → f c = false
def Law80 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b11 = false → c.b13 = false → c.b12 = true → c.b5 = false → c.b4 = true → c.b9 = true → f c = true
def Law81 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b10 = false → c.b0 = true → c.b5 = true → c.b11 = false → c.b8 = false → c.b13 = false → c.b6 = false → c.b9 = false → c.b3 = false → f c = true
def Law82 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b13 = false → c.b1 = false → c.b7 = false → c.b12 = false → c.b3 = true → c.b9 = true → c.b4 = false → c.b0 = true → c.b5 = false → f c = false
def Law83 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b10 = false → c.b0 = true → c.b4 = false → c.b12 = false → c.b7 = false → c.b5 = false → c.b2 = false → c.b6 = false → c.b1 = true → c.b9 = false → c.b11 = true → c.b13 = false → f c = true
def Law84 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b4 = true → c.b12 = true → c.b2 = false → c.b0 = false → c.b11 = false → f c = false
def Law85 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b10 = true → c.b2 = true → c.b0 = false → c.b1 = false → f c = true
def Law86 (f : Decide) : Prop := ∀ c : Case, c.b1 = true → c.b10 = true → c.b13 = false → c.b9 = true → c.b8 = true → c.b11 = true → c.b5 = true → c.b0 = true → c.b2 = true → c.b7 = false → c.b4 = true → f c = false
def Law87 (f : Decide) : Prop := ∀ c : Case, c.b10 = true → c.b3 = false → c.b13 = false → c.b9 = false → c.b0 = true → c.b11 = false → f c = false
def Law88 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b9 = true → c.b4 = true → c.b12 = true → c.b13 = false → c.b11 = true → c.b0 = true → f c = false
def Law89 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b13 = false → c.b5 = true → c.b12 = true → c.b3 = true → c.b6 = false → c.b10 = true → c.b1 = false → c.b4 = true → c.b9 = true → c.b2 = true → c.b11 = false → c.b0 = true → c.b7 = true → f c = false
def Law90 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b7 = true → c.b1 = false → c.b8 = false → c.b5 = true → c.b12 = false → c.b13 = false → c.b3 = false → c.b11 = false → c.b9 = true → c.b4 = false → f c = false
def Law91 (f : Decide) : Prop := ∀ c : Case, c.b2 = false → c.b7 = true → c.b5 = false → c.b0 = false → c.b13 = false → c.b4 = false → f c = false
def Law92 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b5 = false → c.b9 = false → c.b13 = false → c.b2 = false → c.b3 = false → c.b1 = false → c.b11 = true → c.b7 = false → c.b10 = false → c.b0 = true → c.b6 = false → c.b8 = true → c.b4 = false → f c = false
def Law93 (f : Decide) : Prop := ∀ c : Case, c.b0 = false → c.b4 = true → c.b2 = false → c.b12 = false → c.b11 = false → c.b13 = false → f c = false
def Law94 (f : Decide) : Prop := ∀ c : Case, c.b3 = true → c.b0 = true → c.b9 = false → c.b4 = false → c.b10 = false → c.b13 = false → c.b11 = true → c.b5 = true → f c = false
def Law95 (f : Decide) : Prop := ∀ c : Case, c.b7 = false → c.b0 = true → c.b2 = true → c.b13 = false → c.b9 = true → c.b10 = true → c.b1 = false → c.b12 = false → c.b4 = false → c.b5 = false → c.b3 = false → f c = true
def Law96 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b5 = true → c.b2 = false → c.b11 = true → c.b12 = false → c.b6 = false → c.b9 = false → c.b1 = true → c.b10 = false → c.b3 = false → c.b8 = false → c.b4 = true → c.b0 = true → c.b13 = false → f c = true
def Law97 (f : Decide) : Prop := ∀ c : Case, c.b9 = false → c.b13 = false → c.b8 = true → c.b0 = true → c.b2 = false → c.b12 = true → c.b6 = false → c.b1 = true → c.b10 = false → c.b11 = true → c.b5 = true → c.b3 = false → c.b4 = false → c.b7 = true → f c = true
def Law98 (f : Decide) : Prop := ∀ c : Case, c.b10 = false → c.b13 = false → c.b2 = true → c.b5 = true → c.b3 = false → c.b0 = true → c.b11 = false → c.b9 = true → c.b8 = true → f c = false
def Law99 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b6 = false → c.b11 = false → c.b0 = true → c.b9 = true → c.b7 = true → c.b12 = false → c.b4 = false → c.b13 = false → c.b5 = true → c.b3 = true → c.b8 = false → f c = true
def Law100 (f : Decide) : Prop := ∀ c : Case, c.b9 = true → c.b11 = true → c.b4 = false → c.b2 = true → c.b0 = true → c.b3 = false → c.b1 = false → c.b8 = false → c.b13 = false → c.b5 = true → f c = true
def Law101 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b9 = true → c.b13 = false → c.b1 = false → c.b2 = true → c.b5 = false → c.b11 = true → c.b3 = false → c.b4 = false → c.b7 = true → c.b0 = true → f c = false
def Law102 (f : Decide) : Prop := ∀ c : Case, c.b8 = false → c.b4 = true → c.b13 = false → c.b11 = false → c.b0 = true → c.b6 = true → c.b10 = false → c.b9 = false → f c = false
def Law103 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b13 = false → c.b2 = false → c.b4 = false → c.b8 = false → c.b5 = true → c.b9 = true → c.b3 = false → c.b0 = true → c.b11 = true → f c = true
def Law104 (f : Decide) : Prop := ∀ c : Case, c.b12 = false → c.b10 = true → c.b11 = false → c.b0 = true → c.b7 = true → c.b6 = false → c.b2 = true → c.b3 = true → c.b8 = true → c.b4 = false → c.b5 = true → c.b9 = true → c.b13 = false → f c = true
def Law105 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b12 = false → c.b10 = true → c.b6 = true → c.b4 = false → c.b13 = false → c.b5 = true → c.b0 = true → c.b2 = true → c.b9 = true → c.b11 = false → c.b7 = true → f c = true
def Law106 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b6 = false → c.b8 = false → c.b10 = false → c.b4 = false → c.b3 = false → c.b12 = false → c.b1 = false → c.b5 = false → c.b9 = false → c.b2 = false → c.b13 = false → c.b7 = false → c.b0 = true → f c = false
def Law107 (f : Decide) : Prop := ∀ c : Case, c.b6 = true → c.b13 = false → c.b9 = false → c.b10 = false → c.b12 = true → c.b7 = false → c.b5 = true → c.b0 = true → c.b11 = true → c.b3 = false → f c = false
def Law108 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b11 = true → c.b0 = true → c.b2 = true → c.b10 = false → c.b8 = true → c.b9 = true → c.b5 = true → c.b1 = false → c.b7 = true → f c = true
def Law109 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b1 = true → c.b13 = false → c.b4 = true → c.b3 = true → c.b8 = true → c.b10 = false → c.b7 = true → c.b6 = false → c.b9 = true → c.b11 = true → c.b2 = true → c.b5 = true → f c = true
def Law110 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b11 = false → c.b10 = false → c.b4 = false → c.b9 = false → c.b6 = true → c.b8 = false → c.b13 = false → f c = false
def Law111 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b12 = false → c.b1 = true → c.b0 = true → c.b13 = false → c.b11 = false → c.b9 = true → c.b4 = false → c.b8 = false → c.b5 = true → f c = true
def Law112 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b9 = true → c.b12 = true → c.b0 = true → c.b4 = false → c.b5 = false → f c = false
def Law113 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b8 = true → c.b9 = false → c.b6 = true → c.b13 = false → c.b11 = false → c.b10 = false → f c = true
def Law114 (f : Decide) : Prop := ∀ c : Case, c.b2 = true → c.b8 = true → c.b9 = true → c.b7 = false → c.b11 = true → c.b1 = true → c.b5 = true → c.b4 = false → c.b0 = true → c.b13 = false → c.b10 = true → f c = true
def Law115 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b9 = true → c.b13 = false → c.b0 = true → c.b5 = true → c.b2 = false → f c = true
def Law116 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b3 = false → c.b10 = false → c.b4 = false → c.b9 = false → c.b2 = true → c.b11 = true → c.b5 = false → c.b13 = false → c.b12 = true → c.b6 = false → f c = false
def Law117 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b2 = true → c.b0 = true → c.b13 = false → c.b5 = true → c.b4 = true → c.b6 = false → c.b3 = false → c.b11 = false → c.b12 = true → c.b8 = true → c.b10 = true → c.b9 = true → f c = false
def Law118 (f : Decide) : Prop := ∀ c : Case, c.b13 = false → c.b11 = true → c.b4 = false → c.b8 = true → c.b6 = false → c.b10 = false → c.b9 = true → c.b0 = true → c.b7 = true → c.b1 = true → c.b5 = true → c.b2 = true → f c = false
def Law119 (f : Decide) : Prop := ∀ c : Case, c.b0 = true → c.b8 = true → c.b7 = false → c.b10 = true → c.b5 = true → c.b11 = false → c.b13 = false → c.b9 = true → c.b4 = false → c.b6 = false → c.b2 = true → f c = true
def Law120 (f : Decide) : Prop := ∀ c : Case, c.b8 = true → c.b5 = true → c.b11 = false → c.b12 = true → c.b7 = true → c.b2 = true → c.b10 = true → c.b13 = false → c.b0 = true → c.b4 = false → c.b9 = true → f c = true
def Law121 (f : Decide) : Prop := ∀ c : Case, c.b13 = true → c.b12 = true → c.b5 = false → c.b10 = false → c.b2 = false → f c = true
def Law122 (f : Decide) : Prop := ∀ c : Case, c.b5 = false → c.b12 = true → c.b2 = true → c.b13 = true → c.b10 = false → f c = true
def Law123 (f : Decide) : Prop := ∀ c : Case, c.b3 = false → c.b1 = false → c.b7 = true → c.b4 = false → c.b2 = false → c.b12 = false → c.b5 = false → c.b9 = true → c.b0 = true → c.b13 = false → f c = true
def Law124 (f : Decide) : Prop := ∀ c : Case, c.b7 = true → c.b8 = true → c.b3 = false → c.b9 = true → c.b5 = true → c.b2 = true → c.b13 = false → c.b4 = true → c.b11 = true → c.b0 = true → c.b1 = true → c.b10 = false → c.b6 = false → f c = false
def Law125 (f : Decide) : Prop := ∀ c : Case, c.b11 = true → c.b9 = true → c.b0 = true → c.b8 = true → c.b7 = true → c.b10 = true → c.b5 = true → c.b2 = true → c.b13 = false → f c = true
def Law126 (f : Decide) : Prop := ∀ c : Case, c.b1 = false → c.b13 = false → c.b9 = false → c.b10 = false → c.b0 = false → c.b2 = true → f c = true
def Law127 (f : Decide) : Prop := ∀ c : Case, c.b5 = true → c.b13 = false → c.b7 = false → c.b3 = true → c.b2 = true → c.b9 = true → c.b4 = true → c.b6 = false → c.b1 = true → c.b11 = false → c.b10 = true → c.b12 = true → c.b8 = true → c.b0 = true → f c = true



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
  Law31 f ∧
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
  Law47 f ∧
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
  Law63 f ∧
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
  Law79 f ∧
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
  Law95 f ∧
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
  Law111 f ∧
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

end Tbl
