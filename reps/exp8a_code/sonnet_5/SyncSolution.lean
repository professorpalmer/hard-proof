import SyncLaws

open SyncLaws

namespace Sync

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl
theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl
theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem hasId_append_left (r l : List Entry) (i : Nat) (h : hasId r i = true) :
    hasId (r ++ l) i = true := by
  unfold hasId at *; simp only [List.any_append, h, Bool.true_or]

theorem hasIdentity_append_left (r l : List Entry) (a m : Nat) (h : hasIdentity r a m = true) :
    hasIdentity (r ++ l) a m = true := by
  unfold hasIdentity at *; simp only [List.any_append, h, Bool.true_or]

theorem absent_append_false (r l : List Entry) (s : Entry) (h : absent r s = false) :
    absent (r ++ l) s = false := by
  unfold absent at *
  cases h1 : hasId r s.id
  · cases h2 : hasIdentity r s.adapter s.model
    · simp [h1, h2] at h
    · simp [hasIdentity_append_left r l _ _ h2]
  · simp [hasId_append_left r l _ h1]

theorem absent_of_hasId (r : List Entry) (s : Entry) (h : hasId r s.id = true) :
    absent r s = false := by
  unfold absent; rw [h]; rfl

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  have h' : added = (st.filter (absent r)).map (adjust c) := by
    have : r ++ (st.filter (absent r)).map (adjust c) = r ++ added := h
    exact (List.append_cancel_left this).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs hab
  show hasId (r ++ (st.filter (absent r)).map (adjust c)) s.id = true
  unfold hasId
  rw [List.any_append, Bool.or_eq_true]
  right
  rw [List.any_eq_true]
  exact ⟨adjust c s, List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hab⟩, rfl⟩, by simp [adjust_id]⟩

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added he h a ha
  have h' : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left (show r ++ (st.filter (absent r)).map (adjust c) = r ++ added from h)).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  unfold adjust
  split <;> simp_all

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  have h' : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left (show r ++ (st.filter (absent r)).map (adjust c) = r ++ added from h)).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  unfold adjust
  split <;> simp_all

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ he h a ha hl
  have h' : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left (show r ++ (st.filter (absent r)).map (adjust c) = r ++ added from h)).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [he, hl]

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  show r ++ (st.filter (absent r)).map (adjust c) ++
      (st.filter (absent (r ++ (st.filter (absent r)).map (adjust c)))).map (adjust c)
      = r ++ (st.filter (absent r)).map (adjust c)
  have : st.filter (absent (r ++ (st.filter (absent r)).map (adjust c))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    cases hab : absent r s
    · simp [absent_append_false _ _ _ hab]
    · have := ref_nothing_left c st r s hs hab
      have h2 : hasId (r ++ (st.filter (absent r)).map (adjust c)) s.id = true := this
      simp [absent_of_hasId _ _ h2]
  rw [this]; simp

end Sync
