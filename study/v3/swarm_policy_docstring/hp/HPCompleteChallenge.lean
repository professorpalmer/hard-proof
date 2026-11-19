-- hardproof: TOOL-OWNED FILE. The tool writes it again before each check.
import Types
import Laws

open HP

namespace HPComplete

/-- Two designs that pass each law agree on each legal input. -/
theorem laws_complete : ∀ f g : Impl, Passes f → Passes g →
    ∀ x : Input, Legal x → f x = g x := sorry

end HPComplete
