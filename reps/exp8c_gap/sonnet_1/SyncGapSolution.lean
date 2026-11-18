import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

def designA : SyncImpl := refSync

def designB : SyncImpl := fun c st r => refSync c st.reverse r

def config : Config := { locked := fun _ => false, enable := true }
def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩]
def registry : List Entry := []

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
   Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
   Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r; exact Sync.ref_keeps_rows c st.reverse r
  · intro c st r added h a ha
    obtain ⟨s, hs, h2⟩ := Sync.ref_only_absent_starter c st.reverse r added h a ha
    exact ⟨s, List.mem_reverse.mp hs, h2⟩
  · intro c st r s hs ha
    exact Sync.ref_nothing_left c st.reverse r s (List.mem_reverse.mpr hs) ha
  · intro c st r added hen h; exact Sync.ref_disabled_by_default c st.reverse r added hen h
  · intro c st r added h; exact Sync.ref_locked_stays_disabled c st.reverse r added h
  · intro c st r added hd hen h a ha hl
    have hd' : DistinctIds st.reverse := fun s hs s' hs' =>
      hd s (List.mem_reverse.mp hs) s' (List.mem_reverse.mp hs')
    obtain ⟨s, hs, h2⟩ := Sync.ref_enable_keeps_starter_state c st.reverse r added hd' hen h a ha hl
    exact ⟨s, List.mem_reverse.mp hs, h2⟩
  · intro c st r; exact Sync.ref_idempotent c st.reverse r

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp only [starter, List.mem_cons, List.not_mem_nil, or_false] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp_all

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
