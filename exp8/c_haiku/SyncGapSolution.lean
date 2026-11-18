/-
Hard Proof, experiment 8. Adversary solution for the gap challenge.

The seven laws do not fix the order of the appended rows. `designA` appends
the absent starter entries in starter order. `designB` appends the same rows
in reverse order. Both pass all seven laws. On one legal input they give
different registries.
-/
import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The first design: the shipped code, appends the absent starter entries in starter order. -/
def designA : SyncImpl := refSync

/-- The second design: appends the same absent starter entries in reverse order. -/
def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

/-- The input on which the two designs differ. -/
def config : Config := { locked := fun _ => false, enable := true }

def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩]

def registry : List Entry := []

/-! ## Helpers for `designB` -/

theorem added_of_run {c : Config} {st r added : List Entry}
    (h : designB c st r = r ++ added) :
    ((st.filter (absent r)).map (adjust c)).reverse = added :=
  List.append_cancel_left (h : r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added)

theorem mem_of_run {c : Config} {st r added : List Entry} {a : Entry}
    (h : designB c st r = r ++ added) (ha : a ∈ added) :
    ∃ s, s ∈ st ∧ absent r s = true ∧ adjust c s = a := by
  rw [← added_of_run h, List.mem_reverse, List.mem_map] at ha
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨h1, h3⟩ := List.mem_filter.mp hs
  exact ⟨s, h1, h3, rfl⟩

/-! ## The laws hold for `refSync` and for `designB` -/

theorem a_passes : Passes designA := by
  unfold Passes designA
  exact ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
    Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
    Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

theorem b_keeps : KeepsRows designB := by
  intro c st r
  exact ⟨_, rfl⟩

theorem b_only : OnlyAbsentStarter designB := by
  intro c st r added h a ha
  obtain ⟨s, hs, hab, rfl⟩ := mem_of_run h ha
  exact ⟨s, hs, hab, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩

theorem b_nothing : NothingLeft designB := by
  intro c st r s hs ha
  have hmem : adjust c s ∈ ((st.filter (absent r)).map (adjust c)).reverse := by
    rw [List.mem_reverse]
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩
  have hx : hasId ((st.filter (absent r)).map (adjust c)).reverse s.id = true := by
    unfold hasId
    rw [List.any_eq_true]
    exact ⟨adjust c s, hmem, by simp [Sync.adjust_id]⟩
  exact Sync.hasId_append_right r _ s.id hx

theorem b_disabled : DisabledByDefault designB := by
  intro c st r added hen h a ha
  obtain ⟨s, _, _, rfl⟩ := mem_of_run h ha
  exact Sync.adjust_enabled_false c s hen

theorem b_locked : LockedStaysDisabled designB := by
  intro c st r added h a ha hl
  obtain ⟨s, _, _, rfl⟩ := mem_of_run h ha
  rw [Sync.adjust_adapter] at hl
  unfold adjust
  split <;> simp_all

theorem b_enable : EnableKeepsStarterState designB := by
  intro c st r added _ hen h a ha hl
  obtain ⟨s, hs, _, rfl⟩ := mem_of_run h ha
  rw [Sync.adjust_adapter] at hl
  refine ⟨s, hs, (Sync.adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem b_idem : Idempotent designB := by
  intro c st r
  have hnil : st.filter (absent (designB c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs hab
    have hab' : absent (r ++ ((st.filter (absent r)).map (adjust c)).reverse) s = true := hab
    by_cases h : absent r s = true
    · have hmem : adjust c s ∈ ((st.filter (absent r)).map (adjust c)).reverse := by
        rw [List.mem_reverse]
        exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, h⟩, rfl⟩
      have hx : hasId ((st.filter (absent r)).map (adjust c)).reverse s.id = true := by
        unfold hasId
        rw [List.any_eq_true]
        exact ⟨adjust c s, hmem, by simp [Sync.adjust_id]⟩
      have hid := Sync.hasId_append_right r _ s.id hx
      simp [absent, hid] at hab'
    · exact h (Sync.absent_append r _ s hab')
  show designB c st r ++ ((st.filter (absent (designB c st r))).map (adjust c)).reverse
    = designB c st r
  rw [hnil]
  simp

theorem b_passes : Passes designB := by
  unfold Passes
  exact ⟨b_keeps, b_only, b_nothing, b_disabled, b_locked, b_enable, b_idem⟩

/-! ## The input is legal, and the designs differ on it -/

theorem starter_distinct : DistinctIds starter := by
  unfold DistinctIds starter
  decide

theorem differ : designA config starter registry ≠ designB config starter registry := by
  unfold designA designB
  decide

end SyncGap
