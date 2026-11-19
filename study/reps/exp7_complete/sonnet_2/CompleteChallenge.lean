/-
Hard Proof, experiment 7. HUMAN-OWNED FILE.

The completeness challenge. It asks for a proof that the laws leave no behavior
open: two lock designs that pass each law put the same processes in the
critical section after each sequence of events.

The `sorry` is a hole. A prover fills it in `CompleteSolution.lean`.
-/
import Laws

open Laws

namespace Complete

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := sorry

end Complete
