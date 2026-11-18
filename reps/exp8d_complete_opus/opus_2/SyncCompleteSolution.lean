import SyncLaws

open SyncLaws

namespace SyncComplete

theorem entry_eq_of (a b : Entry) (hk : key a = key b) (he : a.enabled = b.enabled) : a = b := by
  cases a; cases b
  simp only [key, Prod.mk.injEq] at hk
  simp_all

theorem key_adjust (c : Config) (s : Entry) : key (adjust c s) = key s := by
  unfold adjust; split <;> simp_all [key]

/-- Two lists with the same keys, matched pairwise by a row law, are equal. -/
theorem map_eq_of_keys (c : Config) :
    ∀ (L added : List Entry), added.map key = L.map key →
      (∀ a ∈ added, ∀ s ∈ L, key a = key s → a = adjust c s) →
      added = L.map (adjust c)
  | [], added, hk, _ => by
    cases added with
    | nil => rfl
    | cons _ _ => simp at hk
  | s :: ss, added, hk, hrow => by
    cases added with
    | nil => simp at hk
    | cons a as =>
      simp only [List.map_cons, List.cons.injEq] at hk
      obtain ⟨hk1, hk2⟩ := hk
      have h1 : a = adjust c s := hrow a (by simp) s (by simp) hk1
      have h2 : as = ss.map (adjust c) :=
        map_eq_of_keys c ss as hk2 (fun a' ha' s' hs' hk' =>
          hrow a' (by simp [ha']) s' (by simp [hs']) hk')
      simp [h1, h2]

/-- Each design that passes every law equals `refSync` on a legal input. -/
theorem passes_eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = refSync c st r := by
  obtain ⟨hkeep, _, _, hdis, hlock, hen, _, hexact⟩ := hf
  obtain ⟨added, hadd⟩ := hkeep c st r
  have hkeys := hexact c st r added hadd
  have hrow : ∀ a ∈ added, ∀ s ∈ st.filter (absent r), key a = key s → a = adjust c s := by
    intro a ha s hs hk
    have hsst : s ∈ st := (List.mem_filter.mp hs).1
    have hid : a.id = s.id := by simp only [key, Prod.mk.injEq] at hk; exact hk.1
    have had : a.adapter = s.adapter := by simp only [key, Prod.mk.injEq] at hk; exact hk.2.1
    apply entry_eq_of a (adjust c s) (by rw [key_adjust]; exact hk)
    cases hce : c.enable with
    | false =>
      have := hdis c st r added hce hadd a ha
      unfold adjust; split <;> simp_all
    | true =>
      cases hl : c.locked a.adapter with
      | true =>
        have := hlock c st r added hadd a ha hl
        unfold adjust; split <;> simp_all
      | false =>
        obtain ⟨s', hs', hid', hen'⟩ := hen c st r added hd hce hadd a ha hl
        have : s' = s := hd s' hs' s hsst (by rw [hid', hid])
        subst this
        unfold adjust; split <;> simp_all
  have := map_eq_of_keys c (st.filter (absent r)) added hkeys hrow
  rw [hadd, this]
  rfl

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [passes_eq_ref f hf c st r hd, passes_eq_ref g hg c st r hd]

end SyncComplete
