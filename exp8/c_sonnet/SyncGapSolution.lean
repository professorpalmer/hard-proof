import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

def designA : SyncImpl := refSync

def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

def config : Config := { locked := fun _ => false, enable := true }
def starter : List Entry := [⟨2, 1, 2, true⟩, ⟨3, 1, 3, true⟩]
def registry : List Entry := []

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
   Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
   Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

private theorem b_added (c : Config) (st r added : List Entry)
    (h : designB c st r = r ++ added) :
    added = ((st.filter (absent r)).map (adjust c)).reverse :=
  (List.append_cancel_left (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm

private theorem b_mem (c : Config) (st r added : List Entry)
    (h : designB c st r = r ++ added) (a : Entry) (ha : a ∈ added) :
    ∃ s, s ∈ st ∧ absent r s = true ∧ a = adjust c s := by
  rw [b_added c st r added h] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hs
  exact ⟨s, h1, h2, rfl⟩

private theorem b_nothing_left : NothingLeft designB := by
  intro c st r s hs ha
  apply Sync.hasId_append_right
  simp only [hasId, List.any_eq_true]
  refine ⟨adjust c s, List.mem_reverse.mpr (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩), ?_⟩
  simp [Sync.adjust_id]

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, b_nothing_left, ?_, ?_, ?_, ?_⟩
  · intro c st r; exact ⟨_, rfl⟩
  · intro c st r added h a ha
    obtain ⟨s, h1, h2, rfl⟩ := b_mem c st r added h a ha
    exact ⟨s, h1, h2, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩
  · intro c st r added hen h a ha
    obtain ⟨s, _, _, rfl⟩ := b_mem c st r added h a ha
    exact Sync.adjust_enabled_false c s hen
  · intro c st r added h a ha hl
    obtain ⟨s, _, _, rfl⟩ := b_mem c st r added h a ha
    rw [Sync.adjust_adapter] at hl
    unfold adjust
    split <;> simp_all
  · intro c st r added _ hen h a ha hl
    obtain ⟨s, h1, _, rfl⟩ := b_mem c st r added h a ha
    rw [Sync.adjust_adapter] at hl
    refine ⟨s, h1, (Sync.adjust_id c s).symm, ?_⟩
    unfold adjust
    simp [hen, hl]
  · intro c st r
    have : st.filter (absent (designB c st r)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s hs hab
      have h1 := Sync.absent_append _ _ _ hab
      have h3 : hasId (designB c st r) s.id = true := b_nothing_left c st r s hs h1
      simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
      rw [hab.1] at h3
      exact absurd h3 (by simp)
    show designB c st r ++ _ = designB c st r
    simp only [this]; simp

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp only [starter, List.mem_cons, List.not_mem_nil, or_false] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp_all

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
