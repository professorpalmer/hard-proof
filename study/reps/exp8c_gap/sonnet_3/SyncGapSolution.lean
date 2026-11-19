import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

def designA : SyncImpl := refSync

/-- Same rows as `refSync`, added in reverse order. -/
def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

def config : Config := { locked := fun _ => false, enable := true }
def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩]
def registry : List Entry := []

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
   Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
   Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

private theorem b_eq (c : Config) (st r added : List Entry)
    (h : designB c st r = r ++ added) :
    added = ((st.filter (absent r)).map (adjust c)).reverse :=
  (List.append_cancel_left (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm

private theorem b_nothing_left : NothingLeft designB := by
  intro c st r s hs ha
  apply Sync.hasId_append_right
  simp only [hasId, List.any_reverse, List.any_map, List.any_eq_true]
  refine ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, ?_⟩
  simp [Sync.adjust_id]

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, b_nothing_left, ?_, ?_, ?_, ?_⟩
  · intro c st r
    exact ⟨_, rfl⟩
  · intro c st r added h a ha
    have hb := b_eq c st r added h
    subst hb
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
    exact ⟨s, hs1, hs2, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩
  · intro c st r added hen h a ha
    have hb := b_eq c st r added h
    subst hb
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    exact Sync.adjust_enabled_false c s hen
  · intro c st r added h a ha hl
    have hb := b_eq c st r added h
    subst hb
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    rw [Sync.adjust_adapter] at hl
    unfold adjust
    split <;> simp_all
  · intro c st r added _ hen h a ha hl
    have hb := b_eq c st r added h
    subst hb
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    rw [Sync.adjust_adapter] at hl
    refine ⟨s, (List.mem_filter.mp hs).1, (Sync.adjust_id c s).symm, ?_⟩
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
    rw [this]; simp

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp only [starter, List.mem_cons, List.not_mem_nil, or_false] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp_all

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
