import SyncLaws

open SyncLaws

namespace SyncComplete

theorem list_eq : ∀ (l1 l2 : List Entry), l1.map key = l2.map key →
    (∀ a ∈ l1, ∀ b ∈ l2, key a = key b → a.enabled = b.enabled) → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l1, b :: l2, h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hk, hl⟩ := h
    have he := hp a (by simp) b (by simp) hk
    have hk' := hk
    simp only [key, Prod.mk.injEq] at hk'
    obtain ⟨h1, h2, h3⟩ := hk'
    have : a = b := by
      cases a; cases b; simp_all
    subst this
    have := list_eq l1 l2 hl (fun x hx y hy => hp x (by simp [hx]) y (by simp [hy]))
    rw [this]

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨k1, o1, _, d1, l1, e1, _, x1⟩ := hf
  obtain ⟨k2, o2, _, d2, l2, e2, _, x2⟩ := hg
  obtain ⟨af, haf⟩ := k1 c st r
  obtain ⟨ag, hag⟩ := k2 c st r
  have hm : af.map key = ag.map key := by
    rw [x1 c st r af haf, x2 c st r ag hag]
  have : af = ag := by
    apply list_eq af ag hm
    intro a ha b hb hkey
    simp only [key, Prod.mk.injEq] at hkey
    obtain ⟨h1, h2, h3⟩ := hkey
    cases hen : c.enable
    · rw [d1 c st r af hen haf a ha, d2 c st r ag hen hag b hb]
    · cases hlk : c.locked a.adapter
      · obtain ⟨s, hs, hsi, hse⟩ := e1 c st r af hd hen haf a ha hlk
        have hlk' : c.locked b.adapter = false := by rw [← h2]; exact hlk
        obtain ⟨s', hs', hsi', hse'⟩ := e2 c st r ag hd hen hag b hb hlk'
        have : s = s' := hd s hs s' hs' (by omega)
        subst this
        rw [hse, hse']
      · have hlk' : c.locked b.adapter = true := by rw [← h2]; exact hlk
        rw [l1 c st r af haf a ha hlk, l2 c st r ag hag b hb hlk']
  rw [haf, hag, this]

end SyncComplete
