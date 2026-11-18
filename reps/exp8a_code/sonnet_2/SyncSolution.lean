import SyncLaws

open SyncLaws

namespace Sync

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem absent_append (r x : List Entry) (s : Entry) (h : absent (r ++ x) s = true) :
    absent r s = true := by
  unfold absent hasId hasIdentity at *
  simp only [List.any_append, Bool.not_or, Bool.and_eq_true] at h
  simp only [Bool.and_eq_true]
  exact ⟨by simpa using h.1.1, by simpa using h.2.1⟩

theorem hasId_append_right (r x : List Entry) (i : Nat) (h : hasId x i = true) :
    hasId (r ++ x) i = true := by
  unfold hasId at *
  simp [List.any_append, h]

theorem added_eq {c : Config} {st r added : List Entry} (h : refSync c st r = r ++ added) :
    added = (st.filter (absent r)).map (adjust c) := by
  unfold refSync at h
  exact (List.append_cancel_left h).symm

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  have h' : added = (st.filter (absent r)).map (adjust c) := added_eq h
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  have := List.mem_filter.mp hs
  exact ⟨s, this.1, this.2, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs ha
  apply hasId_append_right
  unfold hasId
  simp only [List.any_eq_true]
  refine ⟨adjust c s, List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩, ?_⟩
  simp [adjust_id]

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hc h a ha
  have h' : added = (st.filter (absent r)).map (adjust c) := added_eq h
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  unfold adjust
  simp [hc]
  split <;> simp_all

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  have h' : added = (st.filter (absent r)).map (adjust c) := added_eq h
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  unfold adjust
  simp [hl]
  split <;> simp_all

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ he h a ha hl
  have h' : added = (st.filter (absent r)).map (adjust c) := added_eq h
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [he, hl]

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have : st.filter (absent (refSync c st r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs hab
    have h1 := absent_append r _ s hab
    have h2 : hasId (refSync c st r) s.id = true :=
      ref_nothing_left c st r s hs h1
    unfold absent at hab
    simp [h2] at hab
  simp only [refSync] at this ⊢
  rw [this]
  simp

end Sync
