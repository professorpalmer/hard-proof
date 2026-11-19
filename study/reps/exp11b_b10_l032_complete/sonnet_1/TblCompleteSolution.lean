import Tbl
import TblLaws

open Tbl

namespace TblComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19,f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31⟩ := hf
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18,g19,g20,g21,g22,g23,g24,g25,g26,g27,g28,g29,g30,g31⟩ := hg
  unfold Law0 Law1 Law2 Law3 Law4 Law5 Law6 Law7 Law8 Law9 Law10 Law11 Law12 Law13 Law14 Law15 Law16 Law17 Law18 Law19 Law20 Law21 Law22 Law23 Law24 Law25 Law26 Law27 Law28 Law29 Law30 Law31 at *
  rcases c with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> cases b9
  · exact (f11 ⟨false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, false, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, false, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, false, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, false, true, true, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, false, true, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, false, false, true, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, false, false, true, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, false, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, false, false, true, true, true, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, false, false, true, true, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, false, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, false, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, false, true, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, false, true, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, false, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, false, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, false, true, true, true, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, false, true, true, true, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, false, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, false, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, false, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, false, true, true, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, false, true, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f11 ⟨false, true, false, true, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g11 ⟨false, true, false, true, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, false, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, false, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, false, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, false, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, true, false, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, true, true, false⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f30 ⟨false, true, false, true, true, true, true, true, true, true⟩ rfl rfl rfl).trans (g30 ⟨false, true, false, true, true, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, false, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, false, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, false, true, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, false, true, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, false, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, false, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, false, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, false, true, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, false, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, false, true, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, false, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, false, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, false, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, false, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, false, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, false, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, false, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, false, true, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, true, false, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, true, false, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, true, false, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, true, false, true⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, true, true, false⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, true, true, false⟩ rfl rfl).symm
  · exact (f2 ⟨false, true, true, true, true, true, true, true, true, true⟩ rfl rfl).trans (g2 ⟨false, true, true, true, true, true, true, true, true, true⟩ rfl rfl).symm
  · exact (f10 ⟨true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, false, false, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, false, false, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, false, false, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, false, false, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, false, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, false, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f15 ⟨true, false, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g15 ⟨true, false, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f15 ⟨true, false, false, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g15 ⟨true, false, false, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f15 ⟨true, false, false, false, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g15 ⟨true, false, false, false, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f15 ⟨true, false, false, false, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g15 ⟨true, false, false, false, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f10 ⟨true, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, false, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, false, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f1 ⟨true, false, false, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g1 ⟨true, false, false, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f28 ⟨true, false, false, false, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g28 ⟨true, false, false, false, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, false, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, false, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, false, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, false, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f0 ⟨true, false, false, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g0 ⟨true, false, false, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f0 ⟨true, false, false, false, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g0 ⟨true, false, false, false, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, false, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, false, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, false, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, false, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, false, false, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, false, false, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, false, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, false, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, false, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, false, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, false, false, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, false, false, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f13 ⟨true, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g13 ⟨true, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f29 ⟨true, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g29 ⟨true, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, false, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, false, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f10 ⟨true, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f20 ⟨true, false, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g20 ⟨true, false, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f20 ⟨true, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g20 ⟨true, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, true, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, true, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f16 ⟨true, false, false, true, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g16 ⟨true, false, false, true, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f16 ⟨true, false, false, true, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g16 ⟨true, false, false, true, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, true, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, true, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f10 ⟨true, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, true, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, true, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, false, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, false, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, false, true, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, false, true, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f21 ⟨true, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, false, true, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, false, true, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, false, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, false, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, false, true, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, false, true, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, false, true, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, false, true, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f13 ⟨true, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g13 ⟨true, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f29 ⟨true, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g29 ⟨true, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, false, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, false, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, false, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, false, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, false, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, false, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f10 ⟨true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, true, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, true, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, true, false, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, true, false, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f6 ⟨true, false, true, false, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, true, false, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, false, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, false, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f9 ⟨true, false, true, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g9 ⟨true, false, true, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f18 ⟨true, false, true, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g18 ⟨true, false, true, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f9 ⟨true, false, true, false, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g9 ⟨true, false, true, false, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f18 ⟨true, false, true, false, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g18 ⟨true, false, true, false, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f10 ⟨true, false, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, false, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, false, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f5 ⟨true, false, true, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g5 ⟨true, false, true, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f28 ⟨true, false, true, false, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g28 ⟨true, false, true, false, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, true, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, false, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, false, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f0 ⟨true, false, true, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g0 ⟨true, false, true, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f0 ⟨true, false, true, false, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g0 ⟨true, false, true, false, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, false, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, false, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, true, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, true, false, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, false, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, false, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, false, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, true, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f12 ⟨true, false, true, false, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, false, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f25 ⟨true, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f25 ⟨true, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, false, true, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, false, true, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f10 ⟨true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f20 ⟨true, false, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g20 ⟨true, false, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f20 ⟨true, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g20 ⟨true, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, false, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, true, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, true, false, false, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f16 ⟨true, false, true, true, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g16 ⟨true, false, true, true, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f16 ⟨true, false, true, true, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g16 ⟨true, false, true, true, false, false, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, true, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, true, false, false, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, false, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f10 ⟨true, false, true, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, false, true, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, true, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, true, false, true, false, false, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, true, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, true, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, true, true, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, true, true, false, true, false, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f19 ⟨true, false, true, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f17 ⟨true, false, true, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f8 ⟨true, false, true, true, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, true, true, false, true, true, false, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, true, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, true, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f4 ⟨true, false, true, true, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, false, true, true, false, true, true, false, true, true⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f23 ⟨true, false, true, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, false, true, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f14 ⟨true, false, true, true, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, true, false, true, true, true, true, true⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f25 ⟨true, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f25 ⟨true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, false, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, false, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, false, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, false, true, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, true, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, false, true, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, false, true, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, false, true, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, false, true, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, false, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f13 ⟨true, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g13 ⟨true, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f29 ⟨true, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g29 ⟨true, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, false, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, false, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, false, true, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, false, true, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f13 ⟨true, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g13 ⟨true, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f29 ⟨true, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g29 ⟨true, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, false, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, false, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, false, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, false, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, false, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, false, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, false, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, false, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f25 ⟨true, true, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, true, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f25 ⟨true, true, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, true, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f27 ⟨true, true, true, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, false, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, false, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, false, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, false, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, false, true, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, false, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, false, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, false, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, false, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, false, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, false, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, false, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, false, true, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, true, false, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, true, false, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, true, false, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, true, false, true⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, true, true, false⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, true, true, false⟩ rfl rfl rfl).symm
  · exact (f22 ⟨true, true, true, true, false, true, true, true, true, true⟩ rfl rfl rfl).trans (g22 ⟨true, true, true, true, false, true, true, true, true, true⟩ rfl rfl rfl).symm
  · exact (f25 ⟨true, true, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, true, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f25 ⟨true, true, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, true, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, false, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, false, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, false, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, false, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, false, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, true, false, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, true, false, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f26 ⟨true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f24 ⟨true, true, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, true, true, false, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl).symm
  · exact (f3 ⟨true, true, true, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, true, true, true, true, true, true, false, true⟩ rfl rfl rfl rfl rfl).symm
  · exact (f31 ⟨true, true, true, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).trans (g31 ⟨true, true, true, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl).symm
  · exact (f7 ⟨true, true, true, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g7 ⟨true, true, true, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm

end TblComplete
