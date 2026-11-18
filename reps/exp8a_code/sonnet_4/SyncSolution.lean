import SyncLaws

open SyncLaws

namespace Sync

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem hasId_append (r l : List Entry) (i : Nat) :
    hasId (r ++ l) i = (hasId r i || hasId l i) := by
  unfold hasId; rw [List.any_append]

theorem hasIdentity_append (r l : List Entry) (a m : Nat) :
    hasIdentity (r ++ l) a m = (hasIdentity r a m || hasIdentity l a m) := by
  unfold hasIdentity; rw [List.any_append]

theorem hasId_of_mem (l : List Entry) (e : Entry) (h : e ∈ l) : hasId l e.id = true := by
  unfold hasId
  exact List.any_eq_true.mpr ⟨e, h, by simp⟩

theorem added_eq {c : Config} {st r added : List Entry} (h : refSync c st r = r ++ added) :
    added = (st.filter (absent r)).map (adjust c) :=
  (List.append_cancel_left h).symm

theorem ref_keeps_rows : KeepsRows refSync :=
  fun c st r => ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  have h' := added_eq h
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  have := List.mem_filter.mp hs
  exact ⟨s, this.1, this.2, adjust_id c s, adjust_adapter c s,
    adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs ha
  show hasId (r ++ (st.filter (absent r)).map (adjust c)) s.id = true
  rw [hasId_append]
  have hm : adjust c s ∈ (st.filter (absent r)).map (adjust c) :=
    List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩
  have := hasId_of_mem _ _ hm
  rw [adjust_id] at this
  simp [this]

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hen h a ha
  have h' := added_eq h
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  unfold adjust
  split <;> simp_all

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  have h' := added_eq h
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  unfold adjust
  split <;> simp_all

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hen h a ha hl
  have h' := added_eq h
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have key : st.filter (absent (refSync c st r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    by_cases ha : absent r s = true
    · have := ref_nothing_left c st r s hs ha
      unfold absent
      simp [this]
    · have hn' : absent r s = false := by simpa using ha
      unfold absent at hn' ⊢
      show (!hasId (r ++ _) s.id && !hasIdentity (r ++ _) s.adapter s.model) = true → False
      rw [hasId_append, hasIdentity_append]
      intro hh
      revert hn' hh
      cases hasId r s.id <;> cases hasIdentity r s.adapter s.model <;>
        cases hasId (List.map (adjust c) (List.filter (absent r) st)) s.id <;>
        cases hasIdentity (List.map (adjust c) (List.filter (absent r) st)) s.adapter s.model <;>
        simp
  show (r ++ (st.filter (absent r)).map (adjust c)) ++
      (st.filter (absent (refSync c st r))).map (adjust c) = _
  rw [key]; simp; rfl

end Sync
