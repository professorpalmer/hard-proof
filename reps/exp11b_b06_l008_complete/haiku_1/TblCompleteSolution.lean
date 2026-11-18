import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  have key : ∀ (f : Decide), Passes f → ∀ c : Case, f c = (!c.b0 || c.b2) := by
    intro f hf c
    simp only [Passes, Law0, Law1, Law2, Law3, Law4, Law5, Law6, Law7] at hf
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hf
    rcases c with ⟨b0, b1, b2, b3, b4, b5⟩
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp_all
  intro f g hf hg c
  rw [key f hf c, key g hg c]

end TblComplete
