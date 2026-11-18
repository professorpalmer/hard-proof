/-
Hard Proof, experiment 8. HUMAN-OWNED FILE.

The code challenge: prove that the model of the shipped code obeys each law.
Each `sorry` is a hole. The agent fills the holes in `SyncSolution.lean`.
-/
import SyncLaws

open SyncLaws

namespace Sync

theorem ref_keeps_rows : KeepsRows refSync := sorry
theorem ref_only_absent_starter : OnlyAbsentStarter refSync := sorry
theorem ref_nothing_left : NothingLeft refSync := sorry
theorem ref_disabled_by_default : DisabledByDefault refSync := sorry
theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := sorry
theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := sorry
theorem ref_idempotent : Idempotent refSync := sorry
theorem ref_exact_additions : ExactAdditions refSync := sorry

end Sync
