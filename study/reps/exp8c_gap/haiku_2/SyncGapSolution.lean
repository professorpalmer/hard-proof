import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The first design: the shipped model. The appended rows keep starter order. -/
def designA : SyncImpl := refSync

/-- The second design: the same rows, appended in reverse starter order. -/
def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

/-- The input on which the two designs differ. -/
def config : Config := { locked := fun a => a == 2, enable := false }

def starter : List Entry :=
  [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩, ⟨3, 1, 1, true⟩, ⟨4, 2, 5, true⟩]

def registry : List Entry := [⟨1, 1, 1, true⟩]

theorem hasId_reverse (l : List Entry) (i : Nat) (h : hasId l i = true) :
    hasId l.reverse i = true := by
  simp only [hasId, List.any_eq_true] at h ⊢
  obtain ⟨x, hx_mem, hx_id⟩ := h
  exact ⟨x, List.mem_reverse.mpr hx_mem, hx_id⟩

theorem b_keeps : KeepsRows designB := by
  intro c st r
  exact ⟨_, rfl⟩

theorem b_only_absent : OnlyAbsentStarter designB := by
  intro c st r added h a ha
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left
      (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩

theorem b_nothing_left : NothingLeft designB := by
  intro c st r s hs ha
  apply Sync.hasId_append_right
  apply hasId_reverse
  simp only [hasId, List.any_map, List.any_eq_true]
  refine ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, ?_⟩
  simp [Sync.adjust_id]

theorem b_disabled : DisabledByDefault designB := by
  intro c st r added hen h a ha
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left
      (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  exact Sync.adjust_enabled_false c s hen

theorem b_locked : LockedStaysDisabled designB := by
  intro c st r added h a ha hl
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left
      (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  rw [Sync.adjust_adapter] at hl
  unfold adjust
  split <;> simp_all

theorem b_enable : EnableKeepsStarterState designB := by
  intro c st r added _ hen h a ha hl
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left
      (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  rw [Sync.adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, (Sync.adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem b_idempotent : Idempotent designB := by
  intro c st r
  have hnil : st.filter (absent (designB c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs hab
    have h1 := Sync.absent_append _ _ _ hab
    have h2 := b_nothing_left c st r s hs h1
    have h3 : hasId (designB c st r) s.id = true := h2
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    rw [hab.1] at h3
    exact absurd h3 (by simp)
  show designB c st r ++ _ = designB c st r
  simp only [designB] at hnil ⊢
  rw [hnil]
  simp

/-- The first design passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes designA
  exact ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
    Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
    Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

/-- The second design passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes
  exact ⟨b_keeps, b_only_absent, b_nothing_left, b_disabled, b_locked, b_enable, b_idempotent⟩

/-- The input is legal: the starter list has no two entries with one id. -/
theorem starter_distinct : DistinctIds starter := by
  unfold DistinctIds starter
  decide

/-- The two designs give different registries. -/
theorem differ : designA config starter registry ≠ designB config starter registry := by
  unfold designA designB
  decide

end SyncGap
