import Tbl
import TblLaws

open Tbl

namespace TblComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := hf
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := hg
  rcases c with ⟨b0, b1, b2, b3, b4, b5⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
  first
  | exact (f0 _ rfl rfl rfl rfl rfl).trans (g0 _ rfl rfl rfl rfl rfl).symm
  | exact (f1 _ rfl rfl rfl rfl).trans (g1 _ rfl rfl rfl rfl).symm
  | exact (f2 _ rfl rfl rfl rfl rfl).trans (g2 _ rfl rfl rfl rfl rfl).symm
  | exact (f3 _ rfl rfl rfl rfl).trans (g3 _ rfl rfl rfl rfl).symm
  | exact (f4 _ rfl rfl rfl rfl rfl).trans (g4 _ rfl rfl rfl rfl rfl).symm
  | exact (f5 _ rfl rfl rfl rfl rfl).trans (g5 _ rfl rfl rfl rfl rfl).symm
  | exact (f6 _ rfl).trans (g6 _ rfl).symm
  | exact (f7 _ rfl rfl).trans (g7 _ rfl rfl).symm

end TblComplete
