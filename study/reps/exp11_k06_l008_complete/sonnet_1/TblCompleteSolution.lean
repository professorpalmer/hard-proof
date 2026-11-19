import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ c
  cases h1 : c.b1 <;> cases h0 : c.b0 <;> cases h2 : c.b2 <;> cases h4 : c.b4 <;>
    cases h3 : c.b3 <;> cases h5 : c.b5 <;>
    first
    | rw [f0 c h1 h0 h2 h4, g0 c h1 h0 h2 h4]
    | rw [f1 c h1 h0 h2 h4, g1 c h1 h0 h2 h4]
    | rw [f2 c h1 h0 h2, g2 c h1 h0 h2]
    | rw [f3 c h1 h0 h5, g3 c h1 h0 h5]
    | rw [f4 c h1 h0 h5, g4 c h1 h0 h5]
    | rw [f5 c h1 h4, g5 c h1 h4]
    | rw [f6 c h1 h4 h3, g6 c h1 h4 h3]
    | rw [f7 c h1 h4 h3, g7 c h1 h4 h3]

end TblComplete
