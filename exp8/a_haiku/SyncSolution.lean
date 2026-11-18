import SyncLaws

open SyncLaws

namespace Sync

/-! ## Helper lemmas -/

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl

theorem adjust_adapter (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl

theorem adjust_model (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

theorem hasId_append (r X : List Entry) (i : Nat) :
    hasId (r ++ X) i = (hasId r i || hasId X i) := by
  simp [hasId, List.any_append]

theorem hasIdentity_append (r X : List Entry) (a m : Nat) :
    hasIdentity (r ++ X) a m = (hasIdentity r a m || hasIdentity X a m) := by
  simp [hasIdentity, List.any_append]

theorem absent_of_hasId (r : List Entry) (s : Entry) (h : hasId r s.id = true) :
    absent r s = false := by
  simp [absent, h]

/-- Adding rows never makes an absent starter absent again. -/
theorem absent_append_of_false (r X : List Entry) (s : Entry) (h : absent r s = false) :
    absent (r ++ X) s = false := by
  simp only [absent, hasId_append, hasIdentity_append] at h ⊢
  cases hi : hasId r s.id <;> cases hd : hasIdentity r s.adapter s.model <;>
    simp_all

theorem hasId_of_mem_map (c : Config) (l : List Entry) (s : Entry) (h : s ∈ l) :
    hasId (l.map (adjust c)) s.id = true := by
  unfold hasId
  rw [List.any_eq_true]
  exact ⟨adjust c s, List.mem_map_of_mem h, by simp [adjust_id]⟩

theorem filter_eq_nil_of_all {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = false := h a (by simp)
    have hl : l.filter p = [] :=
      filter_eq_nil_of_all p l (fun b hb => h b (by simp [hb]))
    simp [ha, hl]

/-! ## The seven theorems -/

theorem ref_keeps_rows : KeepsRows refSync := by
  intro c st r
  exact ⟨(st.filter (absent r)).map (adjust c), rfl⟩

theorem ref_only_absent_starter : OnlyAbsentStarter refSync := by
  intro c st r added h a ha
  simp only [refSync] at h
  have hadd := List.append_cancel_left h
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  exact ⟨s, hs1, hs2, adjust_id c s, adjust_adapter c s, adjust_model c s⟩

theorem ref_nothing_left : NothingLeft refSync := by
  intro c st r s hs habs
  simp only [refSync]
  rw [hasId_append, hasId_of_mem_map c _ s (List.mem_filter.mpr ⟨hs, habs⟩), Bool.or_true]

theorem ref_disabled_by_default : DisabledByDefault refSync := by
  intro c st r added hen h a ha
  simp only [refSync] at h
  have hadd := List.append_cancel_left h
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  unfold adjust
  split <;> simp_all

theorem ref_locked_stays_disabled : LockedStaysDisabled refSync := by
  intro c st r added h a ha hlock
  simp only [refSync] at h
  have hadd := List.append_cancel_left h
  subst hadd
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  rw [adjust_adapter] at hlock
  unfold adjust
  split <;> simp_all

theorem ref_enable_keeps_starter_state : EnableKeepsStarterState refSync := by
  intro c st r added _ hen h a ha hlock
  simp only [refSync] at h
  have hadd := List.append_cancel_left h
  subst hadd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hs1, _⟩ := List.mem_filter.mp hs
  rw [adjust_adapter] at hlock
  refine ⟨s, hs1, (adjust_id c s).symm, ?_⟩
  simp [adjust, hen, hlock]

theorem ref_idempotent : Idempotent refSync := by
  intro c st r
  simp only [refSync]
  have hnil : st.filter (absent (r ++ (st.filter (absent r)).map (adjust c))) = [] := by
    apply filter_eq_nil_of_all
    intro s hs
    by_cases hab : absent r s = true
    · have hmem : s ∈ st.filter (absent r) := List.mem_filter.mpr ⟨hs, hab⟩
      have hid : hasId (r ++ (st.filter (absent r)).map (adjust c)) s.id = true := by
        rw [hasId_append, hasId_of_mem_map c _ s hmem, Bool.or_true]
      exact absent_of_hasId _ s hid
    · exact absent_append_of_false r _ s (by simpa using hab)
  rw [hnil, List.map_nil, List.append_nil]

end Sync
