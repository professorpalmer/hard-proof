import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The second design: the same rows as `refSync`, but the added rows come in reverse order. -/
def revSync : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

/-- The first design. -/
def designA : SyncImpl := refSync

/-- The second design. -/
def designB : SyncImpl := revSync

/-- The input on which the two designs differ. -/
def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨2, 1, 2, true⟩]
def registry : List Entry := []

theorem hasId_of_mem (L : List Entry) (x : Entry) (h : x ∈ L) : hasId L x.id = true := by
  unfold hasId
  rw [List.any_eq_true]
  exact ⟨x, h, by simp⟩

theorem rev_keeps_rows : KeepsRows revSync := by
  intro c st r
  exact ⟨_, rfl⟩

theorem rev_only_absent_starter : OnlyAbsentStarter revSync := by
  intro c st r added h a ha
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩

theorem rev_nothing_left : NothingLeft revSync := by
  intro c st r s hs ha
  have hm : adjust c s ∈ ((st.filter (absent r)).map (adjust c)).reverse :=
    List.mem_reverse.mpr (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩)
  have h1 := hasId_of_mem _ _ hm
  rw [Sync.adjust_id] at h1
  unfold revSync
  exact Sync.hasId_append_right _ _ _ h1

theorem rev_disabled_by_default : DisabledByDefault revSync := by
  intro c st r added hen h a ha
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  exact Sync.adjust_enabled_false c s hen

theorem rev_locked_stays_disabled : LockedStaysDisabled revSync := by
  intro c st r added h a ha hl
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  rw [Sync.adjust_adapter] at hl
  unfold adjust
  split <;> simp_all

theorem rev_enable_keeps_starter_state : EnableKeepsStarterState revSync := by
  intro c st r added _ hen h a ha hl
  have h' : added = ((st.filter (absent r)).map (adjust c)).reverse :=
    (List.append_cancel_left (show r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ added from h)).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  rw [Sync.adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, (Sync.adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem rev_idempotent : Idempotent revSync := by
  intro c st r
  have hnil : st.filter (absent (revSync c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs hab
    have hab' : absent (r ++ ((st.filter (absent r)).map (adjust c)).reverse) s = true := hab
    have h1 : absent r s = true := Sync.absent_append r _ s hab'
    have h2 : hasId (revSync c st r) s.id = true := rev_nothing_left c st r s hs h1
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    rw [hab.1] at h2
    exact absurd h2 (by decide)
  show revSync c st r ++ _ = revSync c st r
  simp only [revSync] at hnil ⊢
  rw [hnil]
  simp

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
    Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
    Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

theorem b_passes : Passes designB :=
  ⟨rev_keeps_rows, rev_only_absent_starter, rev_nothing_left,
    rev_disabled_by_default, rev_locked_stays_disabled,
    rev_enable_keeps_starter_state, rev_idempotent⟩

theorem starter_distinct : DistinctIds starter := by
  unfold DistinctIds starter
  decide

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
