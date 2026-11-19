import SyncLaws

open SyncLaws

namespace Sync

/-! ## Helper facts about `adjust` -/

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust
  split <;> simp

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust
  split <;> simp

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust
  split <;> simp

/-- With `--enable` off, `adjust` always gives `enabled := false`. -/
theorem adjust_disabled_of_enable_false (c : Config) (s : Entry) (hc : c.enable = false) :
    (adjust c s).enabled = false := by
  unfold adjust
  split <;> simp_all

/-- A locked adapter always gives `enabled := false`. -/
theorem adjust_disabled_of_locked (c : Config) (s : Entry) (hl : c.locked s.adapter = true) :
    (adjust c s).enabled = false := by
  unfold adjust
  split <;> simp_all

/-- With `--enable` on and the adapter not locked, `adjust` keeps the entry. -/
theorem adjust_keep (c : Config) (s : Entry) (hc : c.enable = true)
    (hl : c.locked s.adapter = false) : adjust c s = s := by
  unfold adjust
  have h : (!s.enabled || (c.enable && !c.locked s.adapter)) = true := by
    simp [hc, hl]
  simp [h]

/-! ## Helper facts about `hasId`, `hasIdentity`, `absent` -/

theorem hasId_append (r l : List Entry) (i : Nat) :
    hasId (r ++ l) i = (hasId r i || hasId l i) := by
  unfold hasId
  simp [List.any_append]

theorem hasIdentity_append (r l : List Entry) (a m : Nat) :
    hasIdentity (r ++ l) a m = (hasIdentity r a m || hasIdentity l a m) := by
  unfold hasIdentity
  simp [List.any_append]

/-- Appending rows never makes an absent starter absent again. -/
theorem absent_append_of_false (r l : List Entry) (s : Entry) (h : absent r s = false) :
    absent (r ++ l) s = false := by
  unfold absent at h ⊢
  rw [hasId_append, hasIdentity_append]
  cases hi : hasId r s.id <;> cases hn : hasIdentity r s.adapter s.model <;> simp_all

/-! ## Helper facts about `refSync` -/

theorem refSync_eq (c : Config) (st r : List Entry) :
    refSync c st r = r ++ (st.filter (absent r)).map (adjust c) := rfl

/-- The rows that `refSync` appends, read from its output. -/
theorem added_eq_of (c : Config) (st r added : List Entry)
    (h : refSync c st r = r ++ added) :
    added = (st.filter (absent r)).map (adjust c) := by
  rw [refSync_eq] at h
  exact (List.append_cancel_left h).symm

/-- Each starter that is absent from `r` has an id in the output of `refSync`'s appended rows. -/
theorem hasId_adjust_map (c : Config) (st r : List Entry) (s : Entry) (hs : s ∈ st)
    (h : absent r s = true) :
    hasId ((st.filter (absent r)).map (adjust c)) s.id = true := by
  unfold hasId
  rw [List.any_eq_true]
  refine ⟨adjust c s, List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, h⟩, rfl⟩, ?_⟩
  simp [adjust_id]

theorem hasId_of_absent (c : Config) (st r : List Entry) (s : Entry) (hs : s ∈ st)
    (h : absent r s = true) :
    hasId (refSync c st r) s.id = true := by
  rw [refSync_eq, hasId_append, hasId_adjust_map c st r s hs h, Bool.or_true]

/-- After `refSync`, every starter in `st` is no longer absent. -/
theorem absent_refSync (c : Config) (st r : List Entry) (s : Entry) (hs : s ∈ st) :
    absent (refSync c st r) s = false := by
  cases h : absent r s with
  | true =>
    have hid := hasId_of_absent c st r s hs h
    unfold absent
    simp [hid]
  | false =>
    rw [refSync_eq]
    exact absent_append_of_false r _ s h

/-! ## The seven theorems -/

theorem ref_keeps_rows : KeepsRows refSync := by
  unfold KeepsRows
  intro c st r
  exact ⟨_, refSync_eq c st r⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  unfold OnlyAbsentStarter
  intro c st r added h a ha
  rw [added_eq_of c st r added h] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  unfold NothingLeft
  intro c st r s hs h
  exact hasId_of_absent c st r s hs h

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  unfold DisabledByDefault
  intro c st r added hc h a ha
  rw [added_eq_of c st r added h] at ha
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
  exact adjust_disabled_of_enable_false c s hc

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  unfold LockedStaysDisabled
  intro c st r added h a ha hl
  rw [added_eq_of c st r added h] at ha
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  exact adjust_disabled_of_locked c s hl

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  unfold EnableKeepsStarterState
  intro c st r added _ hc h a ha hl
  rw [added_eq_of c st r added h] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  have hs' : s ∈ st := (List.mem_filter.mp hs).1
  rw [adjust_adapter] at hl
  refine ⟨s, hs', (adjust_id c s).symm, ?_⟩
  rw [adjust_keep c s hc hl]

theorem ref_idempotent : Idempotent refSync := by
  unfold Idempotent
  intro c st r
  have hnil : st.filter (absent (refSync c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    rw [absent_refSync c st r s hs]
    simp
  rw [refSync_eq c st (refSync c st r), hnil]
  simp

end Sync
