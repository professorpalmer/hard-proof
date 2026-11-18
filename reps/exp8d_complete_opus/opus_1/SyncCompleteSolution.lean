import SyncLaws

open SyncLaws

namespace SyncComplete

private theorem entry_eq_of_key {a t : Entry} (hk : key a = key t) (he : a.enabled = t.enabled) :
    a = t := by
  cases a with
  | mk i ad m en =>
    cases t with
    | mk i' ad' m' en' =>
      simp only [key, Prod.mk.injEq] at hk
      obtain ⟨h1, h2, h3⟩ := hk
      simp only at he
      subst h1; subst h2; subst h3; subst he; rfl

private theorem map_eq_of_pointwise (c : Config) :
    ∀ (added fl : List Entry), added.map key = fl.map key →
      (∀ a ∈ added, ∀ t ∈ fl, key a = key t → a = adjust c t) →
      added = fl.map (adjust c)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, t :: ts, h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hk, hrest⟩ := h
    have ha : a = adjust c t := hp a (by simp) t (by simp) hk
    have hr := map_eq_of_pointwise c as ts hrest
      (fun a' ha' t' ht' hk' => hp a' (by simp [ha']) t' (by simp [ht']) hk')
    rw [ha, hr]; rfl

private theorem pointwise (f : SyncImpl) (hf : Passes f) (c : Config) (st r added : List Entry)
    (hd : DistinctIds st) (heq : f c st r = r ++ added) :
    ∀ a ∈ added, ∀ t ∈ st.filter (absent r), key a = key t → a = adjust c t := by
  obtain ⟨_, _, _, h4, h5, h6, _, _⟩ := hf
  intro a ha t ht hk
  have htst : t ∈ st := (List.mem_filter.mp ht).1
  have hid : a.id = t.id := by simp only [key, Prod.mk.injEq] at hk; exact hk.1
  have had : a.adapter = t.adapter := by simp only [key, Prod.mk.injEq] at hk; exact hk.2.1
  apply entry_eq_of_key
  · have hk' := hk
    simp only [key, Prod.mk.injEq] at hk'
    simp only [adjust]; split <;> simp [key, hk']
  · cases hen : c.enable with
    | false =>
      have hae := h4 c st r added hen heq a ha
      simp only [adjust, hen]
      cases htE : t.enabled <;> simp [htE, hae]
    | true =>
      cases hl : c.locked a.adapter with
      | true =>
        have hae := h5 c st r added heq a ha hl
        have hlt : c.locked t.adapter = true := by rw [← had]; exact hl
        simp only [adjust, hen, hlt]
        cases htE : t.enabled <;> simp [htE, hae]
      | false =>
        obtain ⟨s, hs, hsid, hse⟩ := h6 c st r added hd hen heq a ha hl
        have hst : s = t := hd s hs t htst (by rw [hsid, hid])
        subst hst
        have hlt : c.locked s.adapter = false := by rw [← had]; exact hl
        simp only [adjust, hen, hlt]
        cases hsE : s.enabled <;> simp [hsE, hse]

private theorem eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = refSync c st r := by
  obtain ⟨added, heq⟩ := hf.1 c st r
  have h8 := hf.2.2.2.2.2.2.2 c st r added heq
  have hp := pointwise f hf c st r added hd heq
  rw [heq, map_eq_of_pointwise c added _ h8 hp]
  rfl

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [eq_ref f hf c st r hd, eq_ref g hg c st r hd]

end SyncComplete
