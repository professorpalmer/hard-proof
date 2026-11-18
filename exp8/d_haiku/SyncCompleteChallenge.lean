/-
Hard Proof, experiment 8. HUMAN-OWNED FILE.

The completeness challenge for the registry sync laws. It asks for a proof
that the laws leave no behavior open: two sync designs that pass each law give
the same registry for each legal input.

The `sorry` is a hole. A prover fills it in `SyncCompleteSolution.lean`.
-/
import SyncLaws

open SyncLaws

namespace SyncComplete

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := sorry

end SyncComplete
