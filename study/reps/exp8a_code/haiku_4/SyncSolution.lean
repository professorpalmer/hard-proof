import SyncLaws

open SyncLaws

namespace Sync

/-! ## Helpers -/

theorem ref_eq (c : Config) (st r : List Entry) :
    refSync c st r = r ++ (st.filter (absent r)).map (adjust c) := rfl

theorem adj_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust
  split <;> rfl

theorem adj_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust
  split <;> rfl

theorem adj_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust
  split <;> rfl

theorem adj_enabled_false_of_locked (c : Config) (s : Entry) (h : c.locked s.adapter = true) :
    (adjust c s).enabled = false := by
  unfold adjust
  split
  · rename_i hc
    simpa [h] using hc
  · rfl

theorem adj_enabled_false_of_enable_false (c : Config) (s : Entry) (hc : c.enable = false) :
    (adjust c s).enabled = false := by
  unfold adjust
  split
  · rename_i h
    simpa [hc] using h
  · rfl

theorem adj_enabled_eq_of_unlocked (c : Config) (s : Entry) (hen : c.enable = true)
    (hl : c.locked s.adapter = false) : (adjust c s).enabled = s.enabled := by
  unfold adjust
  split
  · rfl
  · rename_i h
    simp [hen, hl] at h

theorem hasId_of_mem {r : List Entry} {e : Entry} (h : e ∈ r) : hasId r e.id = true := by
  unfold hasId
  exact List.any_eq_true.mpr ⟨e, h, by simp⟩

theorem hasId_append_left {r : List Entry} (X : List Entry) {i : Nat}
    (h : hasId r i = true) : hasId (r ++ X) i = true := by
  unfold hasId at h ⊢
  rw [List.any_append]
  simp [h]

theorem hasIdentity_append_left {r : List Entry} (X : List Entry) {a m : Nat}
    (h : hasIdentity r a m = true) : hasIdentity (r ++ X) a m = true := by
  unfold hasIdentity at h ⊢
  rw [List.any_append]
  simp [h]

theorem absent_append_false (r X : List Entry) (s : Entry) (h : absent r s = false) :
    absent (r ++ X) s = false := by
  unfold absent at h ⊢
  have m1 : hasId r s.id = true → hasId (r ++ X) s.id = true :=
    fun h1 => hasId_append_left X h1
  have m2 : hasIdentity r s.adapter s.model = true →
      hasIdentity (r ++ X) s.adapter s.model = true :=
    fun h1 => hasIdentity_append_left X h1
  revert m1 m2 h
  cases hasId r s.id <;> cases hasIdentity r s.adapter s.model <;>
    cases hasId (r ++ X) s.id <;> cases hasIdentity (r ++ X) s.adapter s.model <;> simp_all

theorem filter_nil_of {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = false := h a (by simp)
    have hl : ∀ b ∈ l, p b = false := fun b hb => h b (by simp [hb])
    simp [ha, filter_nil_of p l hl]

theorem added_form {c : Config} {st r added : List Entry}
    (h : refSync c st r = r ++ added) : added = (st.filter (absent r)).map (adjust c) := by
  rw [ref_eq] at h
  exact (List.append_cancel_left h).symm

/-! ## The seven laws for `refSync` -/

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨_, ref_eq c st r⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  have hadd := added_form h
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, adj_id c s, adj_adapter c s, adj_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs h
  rw [ref_eq]
  have hmem : adjust c s ∈ (st.filter (absent r)).map (adjust c) :=
    List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, h⟩, rfl⟩
  have := hasId_of_mem (List.mem_append_right r hmem)
  rwa [adj_id] at this

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hc h a ha
  have hadd := added_form h
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  exact adj_enabled_false_of_enable_false c s hc

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hl
  have hadd := added_form h
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  rw [adj_adapter] at hl
  exact adj_enabled_false_of_locked c s hl

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hen h a ha hl
  have hadd := added_form h
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, _⟩ := List.mem_filter.mp hs
  rw [adj_adapter] at hl
  exact ⟨s, hs1, (adj_id c s).symm, adj_enabled_eq_of_unlocked c s hen hl⟩

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  have hnil : st.filter (absent (refSync c st r)) = [] := by
    apply filter_nil_of
    intro s hs
    cases hA : absent r s with
    | true =>
      have hmem : adjust c s ∈ (st.filter (absent r)).map (adjust c) :=
        List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hA⟩, rfl⟩
      have hid : hasId (refSync c st r) s.id = true := by
        rw [ref_eq]
        have := hasId_of_mem (List.mem_append_right r hmem)
        rwa [adj_id] at this
      unfold absent
      rw [hid]
      rfl
    | false =>
      rw [ref_eq]
      exact absent_append_false r _ s hA
  rw [ref_eq c st (refSync c st r), hnil]
  simp

end Sync
