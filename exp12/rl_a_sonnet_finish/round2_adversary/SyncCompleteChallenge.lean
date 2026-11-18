/-
Hard Proof, experiment 12. HUMAN-OWNED FILE.

The completeness challenge for an agent-written law set (`SyncLaws.lean`).
The `sorry` is a hole. A prover fills it in `SyncCompleteSolution.lean`.
-/
import Sync
import SyncLaws

open Sync

namespace SyncComplete

/-- The laws are complete: two designs that pass each law give the same
registry for each legal input. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := sorry

end SyncComplete
