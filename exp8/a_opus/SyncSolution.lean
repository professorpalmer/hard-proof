import SyncLaws

open SyncLaws

namespace Sync

/-- The added part of `refSync` is exactly the adjusted absent starters. -/
theorem added_eq {c : Config} {st r added : List Entry}
    (h : refSync c st r = r ++ added) :
    added = (st.filter (absent r)).map (adjust c) := by
  unfold refSync at h
  exact (List.append_cancel_left h).symm

theorem mem_added {c : Config} {st r added : List Entry}
    (h : refSync c st r = r ++ added) {a : Entry} (ha : a ∈ added) :
    ∃ s ∈ st, absent r s = true ∧ a = adjust c s := by
  rw [added_eq h] at ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hst, hab⟩ := List.mem_filter.mp hs
  exact ⟨s, hst, hab, rfl⟩

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨_, rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  obtain ⟨s, hs, hab, rfl⟩ := mem_added h ha
  exact ⟨s, hs, hab, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs hab
  unfold hasId refSync
  apply List.any_eq_true.mpr
  refine ⟨adjust c s, ?_, ?_⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hab⟩, rfl⟩
  · simp [adjust_id]

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hc h a ha
  obtain ⟨s, _, _, rfl⟩ := mem_added h ha
  unfold adjust
  cases hse : s.enabled <;> simp [hse, hc]

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  obtain ⟨s, _, _, rfl⟩ := mem_added h ha
  rw [adjust_adapter] at hl
  unfold adjust
  cases hse : s.enabled <;> simp [hse, hl]

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hc h a ha hl
  obtain ⟨s, hs, _, rfl⟩ := mem_added h ha
  rw [adjust_adapter] at hl
  refine ⟨s, hs, (adjust_id c s).symm, ?_⟩
  unfold adjust
  simp [hc, hl]

theorem hasId_append_left {r x : List Entry} {i : Nat} (h : hasId r i = true) :
    hasId (r ++ x) i = true := by
  unfold hasId at *
  rw [List.any_append, h]; rfl

theorem hasIdentity_append_left {r x : List Entry} {a m : Nat} (h : hasIdentity r a m = true) :
    hasIdentity (r ++ x) a m = true := by
  unfold hasIdentity at *
  rw [List.any_append, h]; rfl

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have hnil : st.filter (absent (refSync c st r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    by_cases hab : absent r s = true
    · have := ref_nothing_left c st r s hs hab
      simp [absent, this]
    · simp only [absent, Bool.and_eq_true, Bool.not_eq_true', not_and] at hab
      unfold absent
      cases h1 : hasId r s.id
      · have h2 := hab h1
        cases h3 : hasIdentity r s.adapter s.model
        · simp [h3] at h2
        · simp [hasIdentity_append_left (x := (st.filter (absent r)).map (adjust c)) h3,
            refSync]
      · simp [hasId_append_left (x := (st.filter (absent r)).map (adjust c)) h1, refSync]
  show refSync c st r ++ (st.filter (absent (refSync c st r))).map (adjust c) = refSync c st r
  rw [hnil]; simp

end Sync
