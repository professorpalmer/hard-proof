import SyncLaws

open SyncLaws

namespace Sync

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem added_eq {c : Config} {st r added : List Entry}
    (h : refSync c st r = r ++ added) :
    added = (st.filter (absent r)).map (adjust c) := by
  unfold refSync at h
  exact (List.append_cancel_left h).symm

theorem mem_added {c : Config} {st r added : List Entry}
    (h : refSync c st r = r ++ added) {a : Entry} (ha : a ∈ added) :
    ∃ s ∈ st, absent r s = true ∧ adjust c s = a := by
  rw [added_eq h] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, rfl⟩

theorem ref_keeps_rows : KeepsRows refSync := fun c st r => ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  obtain ⟨s, hs, habs, rfl⟩ := mem_added h ha
  exact ⟨s, hs, habs, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs habs
  unfold refSync hasId
  rw [List.any_append, Bool.or_eq_true]
  right
  rw [List.any_eq_true]
  refine ⟨adjust c s, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, habs⟩, rfl⟩
  · simp [adjust_id]

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hen h a ha
  obtain ⟨s, _, _, rfl⟩ := mem_added h ha
  unfold adjust
  cases hs : s.enabled <;> simp [hs, hen]

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  obtain ⟨s, _, _, rfl⟩ := mem_added h ha
  rw [adjust_adapter] at hl
  unfold adjust
  cases hs : s.enabled <;> simp [hs, hl]

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hen h a ha hl
  obtain ⟨s, hs, _, rfl⟩ := mem_added h ha
  rw [adjust_adapter] at hl
  refine ⟨s, hs, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  show refSync c st r ++ (st.filter (absent (refSync c st r))).map (adjust c) = refSync c st r
  suffices hf : st.filter (absent (refSync c st r)) = [] by
    rw [hf]; simp
  rw [List.filter_eq_nil_iff]
  intro s hs
  cases habs : absent r s
  · unfold absent at habs ⊢
    unfold refSync hasId hasIdentity at *
    simp only [List.any_append, Bool.not_or, Bool.and_eq_false_iff] at habs ⊢
    cases habs with
    | inl h => simp [h]
    | inr h => simp [h]
  · have hid := ref_nothing_left c st r s hs habs
    unfold absent
    simp [hid]

end Sync
