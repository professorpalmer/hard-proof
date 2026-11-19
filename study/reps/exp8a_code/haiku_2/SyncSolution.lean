import SyncLaws

open SyncLaws

namespace Sync

/-! ## Helpers: `hasId`, `hasIdentity`, `absent` under append -/

theorem hasId_append_of (r A : List Entry) (i : Nat) (h : hasId r i = true) :
    hasId (r ++ A) i = true := by
  unfold hasId at *
  rw [List.any_append, h, Bool.true_or]

theorem hasIdentity_append_of (r A : List Entry) (a m : Nat)
    (h : hasIdentity r a m = true) :
    hasIdentity (r ++ A) a m = true := by
  unfold hasIdentity at *
  rw [List.any_append, h, Bool.true_or]

/-- Appending rows never makes a present starter absent again. -/
theorem absent_append_of (r A : List Entry) (s : Entry) (h : absent r s = false) :
    absent (r ++ A) s = false := by
  unfold absent at *
  cases h1 : hasId r s.id
  · cases h2 : hasIdentity r s.adapter s.model
    · simp [h1, h2] at h
    · simp [hasIdentity_append_of r A _ _ h2]
  · simp [hasId_append_of r A _ h1]

/-! ## Helpers: `adjust` -/

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust
  split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust
  split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust
  split <;> rfl

theorem adjust_enabled_false (c : Config) (s : Entry) (hc : c.enable = false) :
    (adjust c s).enabled = false := by
  unfold adjust
  simp only [hc, Bool.and_false, Bool.or_false]
  split <;> simp_all

theorem adjust_enabled_locked (c : Config) (s : Entry) (hl : c.locked s.adapter = true) :
    (adjust c s).enabled = false := by
  unfold adjust
  simp only [hl, Bool.not_true, Bool.and_false, Bool.or_false]
  split <;> simp_all

theorem adjust_keep (c : Config) (s : Entry) (he : c.enable = true)
    (hl : c.locked s.adapter = false) :
    adjust c s = s := by
  unfold adjust
  simp [he, hl]

/-! ## Helpers: the shape of `refSync` -/

theorem refSync_eq_append (c : Config) (st r added : List Entry)
    (h : refSync c st r = r ++ added) :
    (st.filter (absent r)).map (adjust c) = added := by
  have h' : r ++ (st.filter (absent r)).map (adjust c) = r ++ added := h
  exact List.append_cancel_left h'

/-- A starter entry that is absent before the run has its id after the run. -/
theorem hasId_after (c : Config) (st r : List Entry) (s : Entry)
    (hs : s ∈ st) (h : absent r s = true) :
    hasId (refSync c st r) s.id = true := by
  unfold hasId
  show (r ++ (st.filter (absent r)).map (adjust c)).any (fun e => e.id == s.id) = true
  rw [List.any_eq_true]
  refine ⟨adjust c s, ?_, ?_⟩
  · exact List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, h⟩, rfl⟩))
  · simp [adjust_id]

/-- After a run, every starter entry is present, so the filter selects nothing. -/
theorem absent_refSync (c : Config) (st r : List Entry) (s : Entry) (hs : s ∈ st) :
    absent (refSync c st r) s = false := by
  cases hab : absent r s with
  | false => exact absent_append_of r _ s hab
  | true =>
    have hid := hasId_after c st r s hs hab
    unfold absent
    rw [hid]
    simp

/-! ## The seven laws -/

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨(st.filter (absent r)).map (adjust c), rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  have hadd := refSync_eq_append c st r added h
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs h
  exact hasId_after c st r s hs h

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hc h a ha
  have hadd := refSync_eq_append c st r added h
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  exact adjust_enabled_false c s hc

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  have hadd := refSync_eq_append c st r added h
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  exact adjust_enabled_locked c s (by rw [adjust_adapter] at hl; exact hl)

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hc h a ha hl
  have hadd := refSync_eq_append c st r added h
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  have hl' : c.locked s.adapter = false := by
    rw [adjust_adapter] at hl
    exact hl
  refine ⟨s, (List.mem_filter.mp hs).1, (adjust_id c s).symm, ?_⟩
  rw [adjust_keep c s hc hl']

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have hnil : st.filter (absent (refSync c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    simp [absent_refSync c st r s hs]
  show refSync c st r ++ (st.filter (absent (refSync c st r))).map (adjust c)
    = refSync c st r
  rw [hnil, List.map_nil, List.append_nil]

end Sync
