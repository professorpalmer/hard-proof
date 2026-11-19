import SyncLaws

open SyncLaws

namespace Sync

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> simp_all

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> simp_all

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> simp_all

theorem absent_append (r x : List Entry) (s : Entry) (h : absent (r ++ x) s = true) :
    absent r s = true := by
  simp only [absent, hasId, hasIdentity, List.any_append, Bool.not_or, Bool.and_eq_true,
    Bool.not_eq_true'] at h ⊢
  simp_all

theorem hasId_append_right (r x : List Entry) (i : Nat) (h : hasId x i = true) :
    hasId (r ++ x) i = true := by
  simp only [hasId, List.any_append] at h ⊢
  simp [h]

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
  intro c st r s hs ha
  apply hasId_append_right
  simp only [hasId, List.any_map, List.any_eq_true]
  refine ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, ?_⟩
  simp [adjust_id]

theorem adjust_enabled_false (c : Config) (s : Entry) (h : c.enable = false) :
    (adjust c s).enabled = false := by
  unfold adjust; split <;> simp_all

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hen h a ha
  have h' : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left (show r ++ (st.filter (absent r)).map (adjust c) = r ++ added from h)).symm
  subst h'
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  exact adjust_enabled_false c s hen

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
  intro c st r added _ hen h a ha hl
  have h' : added = (st.filter (absent r)).map (adjust c) :=
    (List.append_cancel_left (show r ++ (st.filter (absent r)).map (adjust c) = r ++ added from h)).symm
  subst h'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hl
  refine ⟨s, (List.mem_filter.mp hs).1, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have : st.filter (absent (refSync c st r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs hab
    have h1 := absent_append _ _ _ hab
    have h2 := ref_nothing_left c st r s hs h1
    have h3 : hasId (refSync c st r) s.id = true := h2
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    rw [hab.1] at h3
    exact absurd h3 (by simp)
  show refSync c st r ++ _ = refSync c st r
  simp only [refSync] at this ⊢
  rw [this]; simp

theorem key_adjust (c : Config) (s : Entry) : key (adjust c s) = key s := by
  unfold adjust key
  split <;> rfl

/-- Law 8 holds for the model of the shipped code. -/
theorem ref_exact_additions : ExactAdditions refSync := by
  intro c st r added h
  unfold refSync at h
  have h' := List.append_cancel_left h
  rw [← h', List.map_map]
  apply List.map_congr_left
  intro s _
  exact key_adjust c s

end Sync
