import SyncLaws

open SyncLaws

namespace SyncComplete

theorem key_adjust (c : Config) (s : Entry) : key (adjust c s) = key s := by
  unfold adjust; split <;> rfl

theorem entry_eq (a b : Entry) (hk : key a = key b) (he : a.enabled = b.enabled) : a = b := by
  cases a; cases b
  simp only [key, Prod.mk.injEq] at hk
  simp_all

/-- Aligned lists with equal keys and equal `enabled` fields are equal. -/
theorem eq_of_keys (c : Config) : ∀ (l t : List Entry), l.map key = t.map key →
    (∀ a ∈ l, ∀ s ∈ t, key a = key s → a.enabled = (adjust c s).enabled) →
    l = t.map (adjust c)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, s :: t, h, hen => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hk, ht⟩ := h
    have ha : a = adjust c s :=
      entry_eq _ _ (by rw [key_adjust]; exact hk)
        (hen a (List.mem_cons_self ..) s (List.mem_cons_self ..) hk)
    rw [List.map_cons, ha, eq_of_keys c l t ht
      (fun a' ha' s' hs' hk' => hen a' (List.mem_cons_of_mem _ ha') s' (List.mem_cons_of_mem _ hs') hk')]

/-- Each design that passes the laws is `refSync` on a legal input. -/
theorem eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = refSync c st r := by
  obtain ⟨hkeep, _, _, hdis, hlock, hen, _, hexact⟩ := hf
  obtain ⟨added, hadd⟩ := hkeep c st r
  rw [hadd]
  show r ++ added = r ++ (st.filter (absent r)).map (adjust c)
  congr 1
  apply eq_of_keys c added _ (hexact c st r added hadd)
  intro a ha s hs hk
  have hsst : s ∈ st := (List.mem_filter.mp hs).1
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨hid, had, _⟩ := hk
  cases hce : c.enable with
  | false =>
    rw [hdis c st r added hce hadd a ha]
    unfold adjust; split <;> simp_all
  | true =>
    cases hl : c.locked a.adapter with
    | true =>
      rw [hlock c st r added hadd a ha hl]
      rw [had] at hl
      unfold adjust; split <;> simp_all
    | false =>
      obtain ⟨s', hs', hid', hen'⟩ := hen c st r added hd hce hadd a ha hl
      have : s' = s := hd s' hs' s hsst (by rw [hid', hid])
      subst this
      rw [hen']
      rw [had] at hl
      unfold adjust; simp [hce, hl]

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [eq_ref f hf c st r hd, eq_ref g hg c st r hd]

end SyncComplete
