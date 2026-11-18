import SyncLaws

open SyncLaws

namespace SyncComplete

/-- The added rows of a design are fixed by its laws: the entry for a row
equals the starter entry it copies, with `enabled` taken from that starter entry
under the adjust rule. -/
theorem entry_eq_adjust (c : Config) (x a : Entry) (h1 : a.id = x.id)
    (h2 : a.adapter = x.adapter) (h3 : a.model = x.model)
    (h4 : a.enabled = (x.enabled && c.enable && !c.locked a.adapter)) :
    a = adjust c x := by
  obtain ⟨ai, aa, am, ae⟩ := a
  obtain ⟨xi, xa, xm, xe⟩ := x
  dsimp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  unfold adjust
  split <;> cases xe <;> simp_all

/-- Lemma: when the added rows have the keys of the absent starter entries in
order, and each enabled flag follows its starter entry, the added rows are the
adjusted starter entries. -/
theorem list_eq_adjust : ∀ (c : Config) (st added L : List Entry), DistinctIds st →
    (∀ x ∈ L, x ∈ st) → added.map key = L.map key →
    (∀ a ∈ added, ∀ s ∈ st, s.id = a.id → a.enabled = (s.enabled && c.enable && !c.locked a.adapter)) →
    added = L.map (adjust c) := by
  intro c st added
  induction added with
  | nil =>
    intro L _ _ hk _
    cases L with
    | nil => rfl
    | cons x L' => simp at hk
  | cons a as ih =>
    intro L hd hL hk hen
    cases L with
    | nil => simp at hk
    | cons x L' =>
      simp only [List.map_cons, List.cons.injEq] at hk
      obtain ⟨hkx, hkr⟩ := hk
      have hk1 : a.id = x.id ∧ a.adapter = x.adapter ∧ a.model = x.model := by
        simpa [key] using hkx
      have hxmem : x ∈ st := hL x (List.mem_cons.mpr (Or.inl rfl))
      have hen_a := hen a (List.mem_cons.mpr (Or.inl rfl)) x hxmem hk1.1.symm
      have ha_eq : a = adjust c x :=
        entry_eq_adjust c x a hk1.1 hk1.2.1 hk1.2.2 hen_a
      have hr : as = L'.map (adjust c) :=
        ih L' hd (fun y hy => hL y (List.mem_cons.mpr (Or.inr hy))) hkr
          (fun a' ha' s hs hsid => hen a' (List.mem_cons.mpr (Or.inr ha')) s hs hsid)
      rw [ha_eq, hr]
      rfl

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  have key_lemma : ∀ (f : SyncImpl), Passes f → ∀ (c : Config) (st r : List Entry),
      DistinctIds st → f c st r = r ++ (st.filter (absent r)).map (adjust c) := by
    intro f hf c st r hd
    obtain ⟨hKeep, _, _, hDis, hLock, hEn, _, hExact⟩ := hf
    obtain ⟨added, hadd⟩ := hKeep c st r
    have hA : added = (st.filter (absent r)).map (adjust c) := by
      apply list_eq_adjust c st added (st.filter (absent r)) hd
      · intro x hx
        exact (List.mem_filter.mp hx).1
      · exact hExact c st r added hadd
      · intro a ha s hs hsid
        cases hE : c.enable
        · rw [hDis c st r added hE hadd a ha]
          simp
        · cases hL : c.locked a.adapter
          · obtain ⟨s2, hs2, hid2, hen2⟩ := hEn c st r added hd hE hadd a ha hL
            have hs2s : s2 = s := hd s2 hs2 s hs (hid2.trans hsid.symm)
            rw [hen2, hs2s]
            simp
          · rw [hLock c st r added hadd a ha hL]
            simp
    rw [hadd, hA]
  intro f g hf hg c st r hd
  rw [key_lemma f hf c st r hd, key_lemma g hg c st r hd]

end SyncComplete
