import SyncLaws

open SyncLaws

namespace Sync

/-! ## Helper lemmas about `refSync` -/

theorem refSync_eq (c : Config) (st r : List Entry) :
    refSync c st r = r ++ (st.filter (absent r)).map (adjust c) := rfl

theorem append_left_cancel' {α : Type} (r a b : List α) (h : r ++ a = r ++ b) : a = b := by
  induction r with
  | nil => simpa using h
  | cons x xs ih => exact ih (by simpa using h)

theorem mem_added {c : Config} {st r : List Entry} {a : Entry}
    (h : a ∈ (st.filter (absent r)).map (adjust c)) :
    ∃ s ∈ st, absent r s = true ∧ adjust c s = a := by
  rw [List.mem_map] at h
  obtain ⟨s, hs, rfl⟩ := h
  rw [List.mem_filter] at hs
  exact ⟨s, hs.1, hs.2, rfl⟩

theorem adjust_id (c : Config) (s : Entry) :
    (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
  unfold adjust
  split <;> simp

theorem adjust_disabled (c : Config) (s : Entry) (h : c.enable = false) :
    (adjust c s).enabled = false := by
  unfold adjust
  by_cases h1 : s.enabled <;> simp [h, h1]

theorem adjust_locked_disabled (c : Config) (s : Entry) (hl : c.locked s.adapter = true) :
    (adjust c s).enabled = false := by
  unfold adjust
  by_cases h1 : s.enabled <;> simp [hl, h1]

theorem adjust_unlocked (c : Config) (s : Entry) (he : c.enable = true)
    (hl : c.locked s.adapter = false) : adjust c s = s := by
  unfold adjust
  simp [he, hl]

theorem absent_append_left (r M : List Entry) (s : Entry) (h : absent (r ++ M) s = true) :
    absent r s = true := by
  simp [absent, hasId, hasIdentity, List.any_append] at h ⊢
  exact ⟨h.1.1, h.2.1⟩

theorem absent_eq_false_of_hasId (r : List Entry) (s : Entry) (h : hasId r s.id = true) :
    absent r s = false := by
  unfold absent
  simp [h]

/-! ## Proofs of the seven laws for `refSync` -/

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨_, refSync_eq c st r⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  rw [refSync_eq] at h
  have hadd := append_left_cancel' _ _ _ h
  rw [← hadd] at ha
  obtain ⟨s, hs, habs, rfl⟩ := mem_added ha
  exact ⟨s, hs, habs, adjust_id c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs habs
  have hm : adjust c s ∈ (st.filter (absent r)).map (adjust c) :=
    List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, habs⟩, rfl⟩
  rw [refSync_eq]
  unfold hasId
  rw [List.any_append]
  simp only [Bool.or_eq_true]
  right
  exact List.any_eq_true.mpr ⟨adjust c s, hm, by simp [(adjust_id c s).1]⟩

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hen h a ha
  rw [refSync_eq] at h
  have hadd := append_left_cancel' _ _ _ h
  rw [← hadd] at ha
  obtain ⟨s, _, _, rfl⟩ := mem_added ha
  exact adjust_disabled c s hen

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  rw [refSync_eq] at h
  have hadd := append_left_cancel' _ _ _ h
  rw [← hadd] at ha
  obtain ⟨s, _, _, rfl⟩ := mem_added ha
  have hl' : c.locked s.adapter = true := by
    rw [← (adjust_id c s).2.1]
    exact hl
  exact adjust_locked_disabled c s hl'

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hen h a ha hl
  rw [refSync_eq] at h
  have hadd := append_left_cancel' _ _ _ h
  rw [← hadd] at ha
  obtain ⟨s, hs, _, rfl⟩ := mem_added ha
  have hl' : c.locked s.adapter = false := by
    rw [← (adjust_id c s).2.1]
    exact hl
  exact ⟨s, hs, (adjust_id c s).1.symm, by rw [adjust_unlocked c s hen hl']⟩

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have key : ∀ s ∈ st, absent (r ++ (st.filter (absent r)).map (adjust c)) s = false := by
    intro s hs
    cases h : absent (r ++ (st.filter (absent r)).map (adjust c)) s
    · rfl
    · exfalso
      have hr := absent_append_left r _ s h
      have hm : adjust c s ∈ (st.filter (absent r)).map (adjust c) :=
        List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hr⟩, rfl⟩
      have hid : hasId (r ++ (st.filter (absent r)).map (adjust c)) s.id = true := by
        unfold hasId
        exact List.any_eq_true.mpr
          ⟨adjust c s, List.mem_append.mpr (Or.inr hm), by simp [(adjust_id c s).1]⟩
      rw [absent_eq_false_of_hasId _ _ hid] at h
      simp at h
  have hnil : st.filter (absent (r ++ (st.filter (absent r)).map (adjust c))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    simp [key s hs]
  rw [refSync_eq c st (refSync c st r), refSync_eq c st r, hnil]
  simp

end Sync
