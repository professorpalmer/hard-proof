import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The first design: the shipped code. -/
def designA : SyncImpl := refSync

/-- The second design: the same append, but the starter list is read in reverse
order. Each new row lands in the reverse of starter order. -/
def designB : SyncImpl := fun c st r => refSync c st.reverse r

/-- The input on which the two designs differ. -/
def config : Config := { locked := fun _ => false, enable := false }

def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩]

def registry : List Entry := []

theorem b_passes : Passes designB := by
  unfold Passes designB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r
    exact Sync.ref_keeps_rows c st.reverse r
  · intro c st r added h a ha
    obtain ⟨s, hs, hrest⟩ := Sync.ref_only_absent_starter c st.reverse r added h a ha
    exact ⟨s, List.mem_reverse.mp hs, hrest⟩
  · intro c st r s hs ha
    exact Sync.ref_nothing_left c st.reverse r s (List.mem_reverse.mpr hs) ha
  · intro c st r added hen h a ha
    exact Sync.ref_disabled_by_default c st.reverse r added hen h a ha
  · intro c st r added h a ha hl
    exact Sync.ref_locked_stays_disabled c st.reverse r added h a ha hl
  · intro c st r added hd hen h a ha hl
    have hd' : DistinctIds st.reverse := by
      intro s hs s' hs' hid
      exact hd s (List.mem_reverse.mp hs) s' (List.mem_reverse.mp hs') hid
    obtain ⟨s, hs, hrest⟩ :=
      Sync.ref_enable_keeps_starter_state c st.reverse r added hd' hen h a ha hl
    exact ⟨s, List.mem_reverse.mp hs, hrest⟩
  · intro c st r
    exact Sync.ref_idempotent c st.reverse r

theorem a_passes : Passes designA := by
  unfold designA
  exact ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
    Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
    Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp only [starter, List.mem_cons, List.mem_nil_iff, or_false] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp_all

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
