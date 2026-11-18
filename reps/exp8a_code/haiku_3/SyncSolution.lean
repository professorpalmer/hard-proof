import SyncLaws

open SyncLaws

namespace Sync

/-- The adjusted entry keeps its id, adapter and model. -/
theorem adjust_ident (c : Config) (s : Entry) :
    (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
  unfold adjust
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The adjusted entry is enabled only when it was enabled, `--enable` is set and the lock is off. -/
theorem adjust_enabled (c : Config) (s : Entry) :
    (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
  unfold adjust
  cases hs : s.enabled <;> cases he : c.enable <;> cases hl : c.locked s.adapter <;> simp [hs, he, hl]

theorem hasId_append_of_true (r A : List Entry) (i : Nat) (h : hasId r i = true) :
    hasId (r ++ A) i = true := by
  unfold hasId at *
  rw [List.any_append]
  simp [h]

theorem hasIdentity_append_of_true (r A : List Entry) (a m : Nat)
    (h : hasIdentity r a m = true) : hasIdentity (r ++ A) a m = true := by
  unfold hasIdentity at *
  rw [List.any_append]
  simp [h]

/-- A starter entry whose id is in the registry is not absent. -/
theorem absent_false_of_hasId (r : List Entry) (s : Entry) (h : hasId r s.id = true) :
    absent r s = false := by
  unfold absent
  rw [h]
  simp

/-- A starter entry that is not absent stays not absent when rows are appended. -/
theorem absent_append_of_false (r A : List Entry) (s : Entry) (h : absent r s = false) :
    absent (r ++ A) s = false := by
  have key : hasId r s.id = true ∨ hasIdentity r s.adapter s.model = true := by
    unfold absent at h
    revert h
    cases hasId r s.id <;> cases hasIdentity r s.adapter s.model <;> simp
  rcases key with h1 | h1
  · unfold absent
    rw [hasId_append_of_true r A _ h1]
    simp
  · unfold absent
    rw [hasIdentity_append_of_true r A _ _ h1]
    simp

/-- After the append, every starter entry that was absent has its id in the registry. -/
theorem hasId_after_append (c : Config) (st r : List Entry) (s : Entry)
    (hs : s ∈ st) (habs : absent r s = true) :
    hasId (r ++ (st.filter (absent r)).map (adjust c)) s.id = true := by
  unfold hasId
  rw [List.any_append, Bool.or_eq_true]
  right
  rw [List.any_eq_true]
  exact ⟨adjust c s, List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, habs⟩, rfl⟩,
    by simp [(adjust_ident c s).1]⟩

theorem ref_keeps_rows : KeepsRows refSync := by
  unfold KeepsRows refSync
  intro c st r
  exact ⟨(st.filter (absent r)).map (adjust c), rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  unfold OnlyAbsentStarter refSync
  intro c st r added h a ha
  have hadd : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left h).symm
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, (adjust_ident c s).1, (adjust_ident c s).2.1, (adjust_ident c s).2.2⟩

theorem ref_nothing_left : NothingLeft refSync := by
  unfold NothingLeft refSync
  intro c st r s hs habs
  exact hasId_after_append c st r s hs habs

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  unfold DisabledByDefault refSync
  intro c st r added hen h a ha
  have hadd : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left h).symm
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  simp [adjust_enabled, hen]

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  unfold LockedStaysDisabled refSync
  intro c st r added h a ha hl
  have hadd : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left h).symm
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  have hl' : c.locked s.adapter = true := by
    rw [← (adjust_ident c s).2.1]
    exact hl
  simp [adjust_enabled, hl']

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  unfold EnableKeepsStarterState refSync
  intro c st r added _hd he h a ha hl
  have hadd : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left h).symm
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, _⟩ := List.mem_filter.mp hs
  have hl' : c.locked s.adapter = false := by
    rw [← (adjust_ident c s).2.1]
    exact hl
  exact ⟨s, hs1, (adjust_ident c s).1.symm, by rw [adjust_enabled, he, hl']; simp⟩

theorem ref_idempotent : Idempotent refSync := by
  unfold Idempotent refSync
  intro c st r
  have hnil : st.filter (absent (r ++ (st.filter (absent r)).map (adjust c))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    by_cases hab : absent r s = true
    · have hid := hasId_after_append c st r s hs hab
      rw [absent_false_of_hasId _ s hid]
      simp
    · have hf : absent r s = false := by simpa using hab
      rw [absent_append_of_false r _ s hf]
      simp
  rw [hnil, List.map_nil, List.append_nil]

end Sync
