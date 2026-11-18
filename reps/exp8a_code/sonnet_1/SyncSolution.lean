import SyncLaws

open SyncLaws

namespace Sync

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem hasId_append (r a : List Entry) (i : Nat) :
    hasId (r ++ a) i = (hasId r i || hasId a i) := by
  unfold hasId; rw [List.any_append]

theorem hasIdentity_append (r a : List Entry) (x y : Nat) :
    hasIdentity (r ++ a) x y = (hasIdentity r x y || hasIdentity a x y) := by
  unfold hasIdentity; rw [List.any_append]

theorem hasId_of_mem (a : List Entry) (e : Entry) (h : e ∈ a) : hasId a e.id = true := by
  unfold hasId
  exact List.any_eq_true.mpr ⟨e, h, by simp⟩

theorem refSync_eq (c : Config) (st r : List Entry) :
    refSync c st r = r ++ (st.filter (absent r)).map (adjust c) := rfl

theorem added_eq (c : Config) (st r added : List Entry)
    (h : refSync c st r = r ++ added) : added = (st.filter (absent r)).map (adjust c) := by
  rw [refSync_eq] at h
  exact (List.append_cancel_left h).symm

theorem ref_keeps_rows : KeepsRows refSync := fun c st r => ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  rw [added_eq c st r added h] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  have := List.mem_filter.mp hs
  exact ⟨s, this.1, this.2, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs habs
  rw [refSync_eq, hasId_append]
  have hm : adjust c s ∈ (st.filter (absent r)).map (adjust c) :=
    List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, habs⟩, rfl⟩
  have := hasId_of_mem _ _ hm
  rw [adjust_id] at this
  simp [this]

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hen h a ha
  rw [added_eq c st r added h] at ha
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  unfold adjust
  simp [hen]
  split <;> simp_all

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  rw [added_eq c st r added h] at ha
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  unfold adjust
  simp [hl]
  split <;> simp_all

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hen h a ha hl
  rw [added_eq c st r added h] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, adjust_id c s |>.symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have hnil : st.filter (absent (refSync c st r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    simp only [absent, Bool.not_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    intro hc
    by_cases h : absent r s = true
    · have := ref_nothing_left c st r s hs h
      rw [hc.1] at this; exact absurd this (by simp)
    · have h' : absent r s = false := by simpa using h
      unfold absent at h'
      rw [refSync_eq, hasId_append, hasIdentity_append] at hc
      simp at hc h'
      simp_all
  rw [refSync_eq c st (refSync c st r), hnil]
  simp

end Sync
