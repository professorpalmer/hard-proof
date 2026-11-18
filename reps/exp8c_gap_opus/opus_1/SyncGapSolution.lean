import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The added rows of the shipped code. -/
def newRows (c : Config) (st r : List Entry) : List Entry :=
  (st.filter (absent r)).map (adjust c)

/-- The first design: the shipped code. -/
def designA : SyncImpl := refSync

/-- The second design: the shipped code, but it appends each new row two times. -/
def designB : SyncImpl := fun c st r => r ++ (newRows c st r ++ newRows c st r)

def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 1, 1, true⟩]
def registry : List Entry := []

theorem b_added (c : Config) (st r added : List Entry) (h : designB c st r = r ++ added) :
    added = newRows c st r ++ newRows c st r :=
  (List.append_cancel_left (show r ++ (newRows c st r ++ newRows c st r) = r ++ added from h)).symm

theorem b_mem (c : Config) (st r : List Entry) (a : Entry)
    (ha : a ∈ newRows c st r ++ newRows c st r) :
    ∃ s, s ∈ st ∧ absent r s = true ∧ a = adjust c s := by
  have ha' : a ∈ newRows c st r := by
    rcases List.mem_append.mp ha with h | h <;> exact h
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha'
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, rfl⟩

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
    Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
    Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

theorem b_nothing_left : NothingLeft designB := by
  intro c st r s hs ha
  apply Sync.hasId_append_right
  simp only [hasId, List.any_append, Bool.or_eq_true]
  left
  have := Sync.hasId_append_right ([] : List Entry) (newRows c st r) s.id (by
    simp only [hasId, newRows, List.any_map, List.any_eq_true]
    refine ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, ?_⟩
    simp [Sync.adjust_id])
  simpa [hasId] using this

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, b_nothing_left, ?_, ?_, ?_, ?_⟩
  · intro c st r; exact ⟨_, rfl⟩
  · intro c st r added h a ha
    rw [b_added c st r added h] at ha
    obtain ⟨s, hs, hab, rfl⟩ := b_mem c st r a ha
    exact ⟨s, hs, hab, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩
  · intro c st r added hen h a ha
    rw [b_added c st r added h] at ha
    obtain ⟨s, _, _, rfl⟩ := b_mem c st r a ha
    exact Sync.adjust_enabled_false c s hen
  · intro c st r added h a ha hl
    rw [b_added c st r added h] at ha
    obtain ⟨s, _, _, rfl⟩ := b_mem c st r a ha
    rw [Sync.adjust_adapter] at hl
    unfold adjust
    split <;> simp_all
  · intro c st r added _ hen h a ha hl
    rw [b_added c st r added h] at ha
    obtain ⟨s, hs, _, rfl⟩ := b_mem c st r a ha
    rw [Sync.adjust_adapter] at hl
    refine ⟨s, hs, (Sync.adjust_id c s).symm, ?_⟩
    unfold adjust
    simp [hen, hl]
  · intro c st r
    have : st.filter (absent (designB c st r)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s hs hab
      have h1 := Sync.absent_append _ _ _ hab
      have h3 := b_nothing_left c st r s hs h1
      simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
      rw [hab.1] at h3
      exact absurd h3 (by simp)
    show designB c st r ++ (newRows c st (designB c st r) ++ newRows c st (designB c st r))
      = designB c st r
    simp only [newRows] at this ⊢
    rw [this]; simp

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  rw [hs, hs']

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
