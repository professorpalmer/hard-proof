import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  sorry

end RecoverComplete
