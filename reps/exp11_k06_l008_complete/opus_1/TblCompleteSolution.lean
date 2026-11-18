import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := hf
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := hg
  rcases c with ⟨b0, b1, b2, b3, b4, b5⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    first
    | rw [f0 _ rfl rfl rfl rfl, g0 _ rfl rfl rfl rfl]
    | rw [f1 _ rfl rfl rfl rfl, g1 _ rfl rfl rfl rfl]
    | rw [f2 _ rfl rfl rfl, g2 _ rfl rfl rfl]
    | rw [f3 _ rfl rfl rfl, g3 _ rfl rfl rfl]
    | rw [f4 _ rfl rfl rfl, g4 _ rfl rfl rfl]
    | rw [f5 _ rfl rfl, g5 _ rfl rfl]
    | rw [f6 _ rfl rfl rfl, g6 _ rfl rfl rfl]
    | rw [f7 _ rfl rfl rfl, g7 _ rfl rfl rfl]

end TblComplete
