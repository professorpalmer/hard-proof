import SyncLaws
import SyncSolution

open SyncLaws
open Sync

/-!
The gap. Both designs pass all seven laws. They differ only in the order of the
rows that the command appends. The laws fix which rows are added and what each
row holds, but no law fixes their order. `designB` appends the same rows in
reverse order.
-/

namespace SyncGap

/-- The first design: the shipped code. -/
def designA : SyncImpl := refSync

/-- The second design: the same rows as `refSync`, appended in reverse order. -/
def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

/-- The input on which the two designs differ: no lock, no `--enable`. -/
def config : Config := { locked := fun _ => false, enable := false }

/-- Two starter entries with distinct ids, both absent from the empty registry. -/
def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩]

/-- An empty registry. -/
def registry : List Entry := []

/-! ## Laws for `designB` -/

theorem b_keeps_rows : KeepsRows designB :=
  fun _ _ _ => ⟨_, rfl⟩

theorem b_only_absent_starter : OnlyAbsentStarter designB := by
  intro c st r added h a ha
  have hh : r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added := h
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left hh).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem b_nothing_left : NothingLeft designB := by
  intro c st r s hs ha
  apply hasId_append_right
  unfold hasId
  exact List.any_eq_true.mpr
    ⟨adjust c s,
      List.mem_reverse.mpr (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩),
      by simp [adjust_id]⟩

theorem b_disabled_by_default : DisabledByDefault designB := by
  intro c st r added hen h a ha
  have hh : r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added := h
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left hh).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  exact adjust_enabled_false c s hen

theorem b_locked_stays_disabled : LockedStaysDisabled designB := by
  intro c st r added h a ha hl
  have hh : r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added := h
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left hh).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  rw [adjust_adapter] at hl
  unfold adjust
  split <;> simp_all

theorem b_enable_keeps_starter_state : EnableKeepsStarterState designB := by
  intro c st r added _ hen h a ha hl
  have hh : r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added := h
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left hh).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  rw [adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem b_idempotent : Idempotent designB := by
  intro c st r
  have hnil : st.filter (absent (designB c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs hab
    have h1 := absent_append _ _ _ hab
    have h2 := b_nothing_left c st r s hs h1
    have h3 : hasId (designB c st r) s.id = true := h2
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    rw [hab.1] at h3
    exact absurd h3 (by simp)
  show designB c st r ++ ((st.filter (absent (designB c st r))).map (adjust c)).reverse
    = designB c st r
  rw [hnil]
  simp

/-! ## The four required statements -/

/-- The first design passes each law. -/
theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
    Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
    Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

/-- The second design passes each law. -/
theorem b_passes : Passes designB :=
  ⟨b_keeps_rows, b_only_absent_starter, b_nothing_left,
    b_disabled_by_default, b_locked_stays_disabled,
    b_enable_keeps_starter_state, b_idempotent⟩

/-- The input is legal: the starter list has no two entries with one id. -/
theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp only [starter, List.mem_cons, List.mem_nil_iff, or_false] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp_all

/-- The two designs give different registries. -/
theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
