import Tbl
import TblLaws

open Tbl

namespace TblComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  sorry

end TblComplete
