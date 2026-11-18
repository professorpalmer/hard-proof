import SyncLaws

open SyncLaws

namespace Sync

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem hasId_append_of_mem (r added : List Entry) (a : Entry) (h : a ∈ added) :
    hasId (r ++ added) a.id = true := by
  unfold hasId
  simp only [List.any_eq_true, List.mem_append]
  exact ⟨a, Or.inr h, by simp⟩

theorem hasId_append_left (r added : List Entry) (i : Nat) (h : hasId r i = true) :
    hasId (r ++ added) i = true := by
  unfold hasId at *
  simp only [List.any_eq_true, List.mem_append] at *
  obtain ⟨e, he, h2⟩ := h
  exact ⟨e, Or.inl he, h2⟩

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  have h' : (st.filter (absent r)).map (adjust c) = added :=
    List.append_cancel_left h
  subst h'
  simp only [List.mem_map, List.mem_filter] at ha
  obtain ⟨s, ⟨hs, habs⟩, rfl⟩ := ha
  exact ⟨s, hs, habs, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs habs
  unfold refSync
  have : adjust c s ∈ (st.filter (absent r)).map (adjust c) :=
    List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, habs⟩, rfl⟩
  have h := hasId_append_of_mem r _ _ this
  rw [adjust_id] at h
  exact h

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hen h a ha
  have h' : (st.filter (absent r)).map (adjust c) = added :=
    List.append_cancel_left h
  subst h'
  simp only [List.mem_map] at ha
  obtain ⟨s, _, rfl⟩ := ha
  unfold adjust
  simp only [hen]
  split <;> simp_all

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  have h' : (st.filter (absent r)).map (adjust c) = added :=
    List.append_cancel_left h
  subst h'
  simp only [List.mem_map] at ha
  obtain ⟨s, _, rfl⟩ := ha
  rw [adjust_adapter] at hl
  unfold adjust
  simp only [hl]
  split <;> simp_all

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hen h a ha hl
  have h' : (st.filter (absent r)).map (adjust c) = added :=
    List.append_cancel_left h
  subst h'
  simp only [List.mem_map, List.mem_filter] at ha
  obtain ⟨s, ⟨hs, _⟩, rfl⟩ := ha
  rw [adjust_adapter] at hl
  refine ⟨s, hs, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hen, hl]

theorem absent_mono (r x : List Entry) (s : Entry) (h : absent r s = false) :
    absent (r ++ x) s = false := by
  simp only [absent, hasId, hasIdentity, List.any_append] at h ⊢
  revert h
  cases h1 : r.any (fun e => e.id == s.id) <;> cases h2 : r.any (fun e => e.adapter == s.adapter && e.model == s.model) <;> simp

theorem ref_idempotent: Idempotent refSync := by
  intro c st r
  have key : (st.filter (absent (refSync c st r))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    have : absent (refSync c st r) s = false := by
      by_cases habs : absent r s = true
      · have := ref_nothing_left c st r s hs habs
        unfold absent
        simp [this]
      · exact absent_mono r _ s (by simpa using habs)
    simpa using this
  calc refSync c st (refSync c st r)
      = refSync c st r ++ ((st.filter (absent (refSync c st r))).map (adjust c)) := rfl
    _ = refSync c st r := by rw [key]; simp

end Sync
