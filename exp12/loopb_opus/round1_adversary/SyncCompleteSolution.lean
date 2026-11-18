import Sync
import SyncLaws

open Sync

namespace SyncComplete

/-- No proof: the laws are not complete (see SyncGapSolution.lean). -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  sorry

end SyncComplete
