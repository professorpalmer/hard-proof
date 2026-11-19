import SyncLaws

open SyncLaws

namespace SyncComplete

private theorem list_eq_of_key : ∀ (A B : List Entry), A.map key = B.map key →
    (∀ a ∈ A, ∀ b ∈ B, key a = key b → a.enabled = b.enabled) → A = B := by
  intro A
  induction A with
  | nil =>
    intro B h _
    cases B with
    | nil => rfl
    | cons b B => simp at h
  | cons a A ih =>
    intro B h hen
    cases B with
    | nil => simp at h
    | cons b B =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have he := hen a (by simp) b (by simp) h1
      have : a = b := by
        obtain ⟨ai, aa, am, ae⟩ := a
        obtain ⟨bi, ba, bm, be⟩ := b
        simp only [key, Prod.mk.injEq] at h1
        simp only at he
        obtain ⟨h1a, h1b, h1c⟩ := h1
        subst h1a; subst h1b; subst h1c; subst he; rfl
      subst this
      rw [ih B h2 (fun x hx y hy => hen x (by simp [hx]) y (by simp [hy]))]

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hg
  obtain ⟨A, hA⟩ := f1 c st r
  obtain ⟨B, hB⟩ := g1 c st r
  rw [hA, hB]
  congr 1
  apply list_eq_of_key
  · rw [f8 c st r A hA, g8 c st r B hB]
  · intro a ha b hb hk
    simp only [key, Prod.mk.injEq] at hk
    obtain ⟨k1, k2, k3⟩ := hk
    cases hen : c.enable with
    | false =>
      rw [f4 c st r A hen hA a ha, g4 c st r B hen hB b hb]
    | true =>
      cases hl : c.locked a.adapter with
      | true =>
        rw [f5 c st r A hA a ha hl, g5 c st r B hB b hb (by rw [← k2]; exact hl)]
      | false =>
        obtain ⟨s, hs, hsi, hse⟩ := f6 c st r A hd hen hA a ha hl
        obtain ⟨s', hs', hsi', hse'⟩ := g6 c st r B hd hen hB b hb (by rw [← k2]; exact hl)
        have : s = s' := hd s hs s' hs' (by rw [hsi, hsi', k1])
        subst this
        rw [hse, hse']

end SyncComplete
