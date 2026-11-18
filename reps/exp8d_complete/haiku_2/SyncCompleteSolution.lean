import SyncLaws

open SyncLaws

namespace SyncComplete

theorem adjust_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> simp_all

theorem adjust_enabled_false_of_enable_false (c : Config) (s : Entry) (h : c.enable = false) :
    (adjust c s).enabled = false := by
  unfold adjust; split <;> simp_all

theorem adjust_enabled_false_of_locked (c : Config) (s : Entry) (h : c.locked s.adapter = true) :
    (adjust c s).enabled = false := by
  unfold adjust; split <;> simp_all

theorem adjust_enabled_of_unlocked (c : Config) (s : Entry) (he : c.enable = true)
    (h : c.locked s.adapter = false) : (adjust c s).enabled = s.enabled := by
  unfold adjust; split <;> simp_all

theorem key_adjust (c : Config) (s : Entry) : key (adjust c s) = key s := by
  unfold adjust key; split <;> rfl

/-- Under laws 4, 5, 6 and 8, each added row has the `enabled` value that
`adjust` gives its starter entry. -/
theorem added_enabled (f : SyncImpl) (hf : Passes f) (c : Config) (st r added : List Entry)
    (hd : DistinctIds st) (h : f c st r = r ++ added) :
    ∀ a ∈ added, ∀ s ∈ st, s.id = a.id → a.enabled = (adjust c s).enabled := by
  obtain ⟨_, _, _, hDis, hLock, hEn, _, hExact⟩ := hf
  intro a ha s hs hid
  have hmem : key a ∈ (st.filter (absent r)).map key := by
    rw [← hExact c st r added h]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨t, ht, hkt⟩ := List.mem_map.mp hmem
  have hts : t ∈ st := (List.mem_filter.mp ht).1
  have htid : t.id = a.id := congrArg (fun p => p.1) hkt
  have htad : t.adapter = a.adapter := congrArg (fun p => p.2.1) hkt
  have hts_eq : t = s := hd t hts s hs (htid.trans hid.symm)
  have hsad : s.adapter = a.adapter := by
    rw [← hts_eq]; exact htad
  by_cases hen : c.enable = true
  · by_cases hl : c.locked a.adapter = true
    · rw [hLock c st r added h a ha hl, adjust_enabled_false_of_locked c s (by rw [hsad]; exact hl)]
    · have hl' : c.locked a.adapter = false := Bool.eq_false_iff.mpr hl
      obtain ⟨u, hu, huid, hae⟩ := hEn c st r added hd hen h a ha hl'
      have hu_eq : u = s := hd u hu s hs (huid.trans hid.symm)
      rw [hae, hu_eq, adjust_enabled_of_unlocked c s hen (by rw [hsad]; exact hl')]
  · have hen' : c.enable = false := Bool.eq_false_iff.mpr hen
    rw [hDis c st r added hen' h a ha, adjust_enabled_false_of_enable_false c s hen']

/-- Two lists with the same keys, whose entries have the enabled value that
`adjust` gives, are equal. -/
theorem pair_eq (c : Config) (st : List Entry) : ∀ (X Y : List Entry),
    X.map key = Y.map key →
    (∀ x ∈ X, ∀ s ∈ st, s.id = x.id → x.enabled = (adjust c s).enabled) →
    (∀ y ∈ Y, ∃ s ∈ st, s.id = y.id ∧ y.enabled = (adjust c s).enabled) → X = Y
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, h, hX, hY => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    obtain ⟨hk, ht⟩ := h
    obtain ⟨s, hs, hid, hen⟩ := hY y (by simp)
    have hxid : x.id = y.id := congrArg (fun p => p.1) hk
    have hxy : x.enabled = y.enabled :=
      (hX x (by simp) s hs (hid.trans hxid.symm)).trans hen.symm
    have hxe : x = y := by
      have hxa : x.adapter = y.adapter := congrArg (fun p => p.2.1) hk
      have hxm : x.model = y.model := congrArg (fun p => p.2.2) hk
      cases x
      cases y
      dsimp only at hxid hxa hxm hxy
      subst hxid hxa hxm hxy
      rfl
    have hrest := pair_eq c st xs ys ht
      (fun x' hx' s' hs' hsid => hX x' (by simp [hx']) s' hs' hsid)
      (fun y' hy' => hY y' (by simp [hy']))
    rw [hxe, hrest]

/-- A passing design adds exactly the `adjust` of the absent starter entries. -/
theorem passes_eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = r ++ (st.filter (absent r)).map (adjust c) := by
  have hf' := hf
  obtain ⟨hK, _, _, _, _, _, _, hExact⟩ := hf'
  obtain ⟨added, h⟩ := hK c st r
  rw [h]
  congr 1
  apply pair_eq c st added ((st.filter (absent r)).map (adjust c))
  · rw [hExact c st r added h]
    simp [List.map_map, key_adjust]
  · intro a ha s hs hid
    exact added_enabled f hf c st r added hd h a ha s hs hid
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
    exact ⟨s, (List.mem_filter.mp hs).1, (adjust_id c s).symm, rfl⟩

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [passes_eq_ref f hf c st r hd, passes_eq_ref g hg c st r hd]

end SyncComplete
