/-
Hard Proof, experiment 12. HUMAN-OWNED FILE.

The gap challenge for an agent-written law set (`SyncLaws.lean`).
Each `sorry` is a hole. The adversary fills the holes in `SyncGapSolution.lean`.
-/
import Sync
import SyncLaws

open Sync

namespace SyncGap

/-- The first design. -/
def designA : SyncImpl := sorry

/-- The second design. -/
def designB : SyncImpl := sorry

/-- The input on which the two designs differ. -/
def config : Config := sorry
def starter : List Entry := sorry
def registry : List Entry := sorry

/-- The first design passes each law. -/
theorem a_passes : Passes designA := sorry

/-- The second design passes each law. -/
theorem b_passes : Passes designB := sorry

/-- The input is legal: the starter list has no two entries with one id. -/
theorem starter_distinct : DistinctIds starter := sorry

/-- The two designs give different registries. -/
theorem differ : designA config starter registry ≠ designB config starter registry := sorry

end SyncGap
