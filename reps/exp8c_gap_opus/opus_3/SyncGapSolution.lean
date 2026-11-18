import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The first design: the model of the shipped code. -/
def designA : SyncImpl := refSync

/-- The second design: the same new entries, in reverse order. -/
def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

/-- The input on which the two designs differ. -/
def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 1, 1, false⟩, ⟨2, 1, 2, false⟩]
def registry : List Entry := []

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
   Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
   Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

theorem b_added (c : Config) (st r added : List Entry) (h : designB c st r = r ++ added) :
    added = ((st.filter (absent r)).map (adjust c)).reverse :=
  (List.append_cancel_left
    (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm

theorem b_mem (c : Config) (st r : List Entry) (a : Entry)
    (ha : a ∈ ((st.filter (absent r)).map (adjust c)).reverse) :
    ∃ s, (s ∈ st ∧ absent r s = true) ∧ adjust c s = a := by
  rw [List.mem_reverse] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  exact ⟨s, List.mem_filter.mp hs, rfl⟩

theorem b_keeps_rows : KeepsRows designB := by
  intro c st r
  exact ⟨_, rfl⟩

theorem b_only_absent_starter : OnlyAbsentStarter designB := by
  intro c st r added h a ha
  rw [b_added c st r added h] at ha
  obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := b_mem c st r a ha
  exact ⟨s, hs1, hs2, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩

theorem b_nothing_left : NothingLeft designB := by
  intro c st r s hs ha
  apply Sync.hasId_append_right
  simp only [hasId, List.any_reverse, List.any_map, List.any_eq_true]
  refine ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, ?_⟩
  simp [Sync.adjust_id]

theorem b_disabled_by_default : DisabledByDefault designB := by
  intro c st r added hen h a ha
  rw [b_added c st r added h] at ha
  obtain ⟨s, _, rfl⟩ := b_mem c st r a ha
  exact Sync.adjust_enabled_false c s hen

theorem b_locked_stays_disabled : LockedStaysDisabled designB := by
  intro c st r added h a ha hl
  rw [b_added c st r added h] at ha
  obtain ⟨s, _, rfl⟩ := b_mem c st r a ha
  rw [Sync.adjust_adapter] at hl
  unfold adjust
  split <;> simp_all

theorem b_enable_keeps_starter_state : EnableKeepsStarterState designB := by
  intro c st r added _ hen h a ha hl
  rw [b_added c st r added h] at ha
  obtain ⟨s, ⟨hs, _⟩, rfl⟩ := b_mem c st r a ha
  rw [Sync.adjust_adapter] at hl
  refine ⟨s, hs, (Sync.adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem b_idempotent : Idempotent designB := by
  intro c st r
  have : st.filter (absent (designB c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs hab
    have h1 := Sync.absent_append _ _ _ hab
    have h3 := b_nothing_left c st r s hs h1
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    rw [hab.1] at h3
    exact absurd h3 (by simp)
  show designB c st r ++ _ = designB c st r
  rw [this]; simp

theorem b_passes : Passes designB :=
  ⟨b_keeps_rows, b_only_absent_starter, b_nothing_left, b_disabled_by_default,
   b_locked_stays_disabled, b_enable_keeps_starter_state, b_idempotent⟩

theorem starter_distinct : DistinctIds starter := by
  unfold DistinctIds starter
  decide

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
