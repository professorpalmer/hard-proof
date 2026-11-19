import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- Every rule that passes the laws equals the reference rule on each case. -/
theorem passes_eq_ref : ∀ (k : Decide), Passes k → ∀ c : Case, k c = Tbl.ref c := by
  intro k hk c
  simp only [Passes, Leaf0, Leaf1, Leaf2, Leaf3, Leaf4, Leaf5, Leaf6, Leaf7] at hk
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hk
  rcases c with ⟨b0, b1, b2, b3, b4, b5⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    simp [Tbl.ref, h0, h1, h2, h3, h4, h5, h6, h7]

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  rw [passes_eq_ref f hf c, passes_eq_ref g hg c]

end TblComplete
