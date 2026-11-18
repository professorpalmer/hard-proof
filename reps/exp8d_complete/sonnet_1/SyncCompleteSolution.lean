import SyncLaws

open SyncLaws

namespace SyncComplete

theorem elem_eq (f : SyncImpl) (hp : Passes f) (c : Config) (st r added : List Entry)
    (hd : DistinctIds st) (hf : f c st r = r ++ added) (a s : Entry) (ha : a ∈ added)
    (hs : s ∈ st) (hk : key a = key s) : a = adjust c s := by
  obtain ⟨_, _, _, h4, h5, h6, _, _⟩ := hp
  have hi : a.id = s.id := congrArg Prod.fst hk
  have hadp : a.adapter = s.adapter := congrArg (fun p => p.2.1) hk
  have hm : a.model = s.model := congrArg (fun p => p.2.2) hk
  have e5 := h5 c st r added hf a ha
  have e4 := h4 c st r added
  have e6 := h6 c st r added hd
  cases hen : c.enable <;> cases hl : c.locked s.adapter
  · have : a.enabled = false := e4 hen hf a ha
    unfold adjust; rw [hen, hl]
    cases hse : s.enabled <;> simp <;> (cases a; cases s; simp_all)
  · have : a.enabled = false := e4 hen hf a ha
    unfold adjust; rw [hen, hl]
    cases hse : s.enabled <;> simp <;> (cases a; cases s; simp_all)
  · obtain ⟨s', hs', hid, he⟩ := e6 hen hf a ha (by rw [hadp]; exact hl)
    have hss : s' = s := hd s' hs' s hs (by rw [hid, hi])
    subst hss
    unfold adjust; rw [hen, hl]
    simp
    cases a; cases s'; simp_all
  · have : a.enabled = false := e5 (by rw [hadp]; exact hl)
    unfold adjust; rw [hen, hl]
    cases hse : s.enabled <;> simp <;> (cases a; cases s; simp_all)

theorem list_eq (f : SyncImpl) (hp : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) (added : List Entry) (hf : f c st r = r ++ added) :
    ∀ L : List Entry, (∀ s ∈ L, s ∈ st) → ∀ B : List Entry, (∀ a ∈ B, a ∈ added) →
      B.map key = L.map key → B = L.map (adjust c) := by
  intro L
  induction L with
  | nil =>
    intro _ B _ h
    cases B with
    | nil => rfl
    | cons b bs => simp at h
  | cons s L ih =>
    intro hL B hB h
    cases B with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨elem_eq f hp c st r added hd hf b s (hB b (by simp)) (hL s (by simp)) h.1, ?_⟩
      exact ih (fun x hx => hL x (by simp [hx])) bs (fun x hx => hB x (by simp [hx])) h.2

theorem eq_ref (f : SyncImpl) (hp : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = refSync c st r := by
  obtain ⟨⟨added, hf⟩, _⟩ := And.intro (hp.1 c st r) hp
  have hx := hp.2.2.2.2.2.2.2 c st r added hf
  have := list_eq f hp c st r hd added hf (st.filter (absent r))
    (fun s hs => (List.mem_filter.mp hs).1) added (fun a ha => ha) hx
  rw [hf, this]; rfl

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [eq_ref f hf c st r hd, eq_ref g hg c st r hd]

end SyncComplete
