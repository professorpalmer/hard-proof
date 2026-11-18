/-
Hard Proof, experiment 11. Adversary solution for the completeness check.

Claim: the laws are complete. Every one of the 1024 cases is fixed by at
least one law, and no two laws that fire on one case disagree. So two rules
that pass every law agree on every case. The proof splits the case into its
ten concrete values and rewrites with the laws.
-/
import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg
  unfold Passes Law0 Law1 Law2 Law3 Law4 Law5 Law6 Law7 Law8 Law9 Law10 Law11 Law12 Law13 Law14 Law15 Law16 Law17 Law18 Law19 Law20 Law21 Law22 Law23 Law24 Law25 Law26 Law27 Law28 Law29 Law30 Law31 at hf hg
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
    f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31⟩ := hf
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15,
    g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31⟩ := hg
  intro c
  rcases c with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;>
    simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
      f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31,
      g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15,
      g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31]

end TblComplete
