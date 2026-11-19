import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

/-- Not provable: the laws leave `pidKnown = false, age = none` free.
See `RecoverGapSolution.lean`. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := sorry

end RecoverComplete
