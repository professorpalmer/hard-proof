import SyncLaws

open SyncLaws

namespace SyncComplete

theorem list_eq : ∀ (l1 l2 : List Entry), l1.map key = l2.map key →
    (∀ a ∈ l1, ∀ b ∈ l2, key a = key b → a.enabled = b.enabled) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h _; cases l2 with
    | nil => rfl
    | cons b t => simp at h
  | cons a t ih =>
    intro l2 h hen
    cases l2 with
    | nil => simp at h
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hk, ht⟩ := h
      have he := hen a (by simp) b (by simp) hk
      have : t = u := ih u ht (fun x hx y hy => hen x (by simp [hx]) y (by simp [hy]))
      subst this
      obtain ⟨i, ad, m, e⟩ := a
      obtain ⟨i', ad', m', e'⟩ := b
      simp only [key, Prod.mk.injEq] at hk
      simp only at he
      obtain ⟨h1, h2, h3⟩ := hk
      subst h1; subst h2; subst h3; subst he
      rfl

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hg
  obtain ⟨af, haf⟩ := f1 c st r
  obtain ⟨ag, hag⟩ := g1 c st r
  rw [haf, hag]
  congr 1
  apply list_eq
  · rw [f8 c st r af haf, g8 c st r ag hag]
  · intro a ha b hb hk
    simp only [key, Prod.mk.injEq] at hk
    obtain ⟨h1, h2, h3⟩ := hk
    cases hen : c.enable
    · rw [f4 c st r af hen haf a ha, g4 c st r ag hen hag b hb]
    · cases hl : c.locked a.adapter
      · have hl' : c.locked b.adapter = false := by rw [← h2]; exact hl
        obtain ⟨s, hs, hsi, hse⟩ := f6 c st r af hd hen haf a ha hl
        obtain ⟨s', hs', hsi', hse'⟩ := g6 c st r ag hd hen hag b hb hl'
        have : s = s' := hd s hs s' hs' (by rw [hsi, hsi', h1])
        subst this
        rw [hse, hse']
      · have hl' : c.locked b.adapter = true := by rw [← h2]; exact hl
        rw [f5 c st r af haf a ha hl, g5 c st r ag hag b hb hl']

end SyncComplete
