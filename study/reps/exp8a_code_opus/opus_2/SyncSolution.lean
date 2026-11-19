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
    ∃ s ∈ st, absent r s = true ∧ a = adjust c s := by
  rw [added_eq h] at ha
  simp only [List.mem_map, List.mem_filter] at ha
  obtain ⟨s, ⟨hs, hab⟩, rfl⟩ := ha
  exact ⟨s, hs, hab, rfl⟩

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  obtain ⟨s, hs, hab, rfl⟩ := mem_added h ha
  exact ⟨s, hs, hab, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs hab
  unfold refSync hasId
  rw [List.any_eq_true]
  refine ⟨adjust c s, ?_, ?_⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hab⟩, rfl⟩
  · simp [adjust_id]

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hc h a ha
  obtain ⟨s, _, _, rfl⟩ := mem_added h ha
  unfold adjust
  split
  · rename_i hif
    simp [hc] at hif
    exact hif
  · rfl

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  obtain ⟨s, _, _, rfl⟩ := mem_added h ha
  rw [adjust_adapter] at hl
  unfold adjust
  split
  · rename_i hif
    simp [hl] at hif
    exact hif
  · rfl

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hc h a ha hl
  obtain ⟨s, hs, _, rfl⟩ := mem_added h ha
  rw [adjust_adapter] at hl
  refine ⟨s, hs, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hc, hl]

theorem absent_append {r x : List Entry} {s : Entry} (h : absent (r ++ x) s = true) :
    absent r s = true := by
  unfold absent hasId hasIdentity at *
  simp only [List.any_append, Bool.not_or, Bool.and_eq_true] at h
  simp only [Bool.and_eq_true]
  exact ⟨h.1.1, h.2.1⟩

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  suffices hf : st.filter (absent (refSync c st r)) = [] by
    show refSync c st r ++ _ = _
    rw [hf]; simp
  rw [List.filter_eq_nil_iff]
  intro s hs hab
  have hr : absent r s = true := by
    unfold refSync at hab
    exact absent_append hab
  have hid := ref_nothing_left c st r s hs hr
  unfold absent at hab
  simp [hid] at hab

end Sync
