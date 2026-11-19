import SyncLaws

open SyncLaws

namespace SyncComplete

theorem list_eq_of_key : ∀ (A B : List Entry), A.map key = B.map key →
    (∀ a ∈ A, ∀ b ∈ B, key a = key b → a = b) → A = B
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: A, b :: B, h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab := hp a (by simp) b (by simp) h.1
    subst hab
    have := list_eq_of_key A B h.2 (fun x hx y hy hk => hp x (by simp [hx]) y (by simp [hy]) hk)
    rw [this]

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨k1f, o2f, _, d4f, l5f, e6f, _, x8f⟩ := hf
  obtain ⟨k1g, o2g, _, d4g, l5g, e6g, _, x8g⟩ := hg
  obtain ⟨A, hA⟩ := k1f c st r
  obtain ⟨B, hB⟩ := k1g c st r
  have kA := x8f c st r A hA
  have kB := x8g c st r B hB
  suffices h : A = B by rw [hA, hB, h]
  apply list_eq_of_key A B (kA.trans kB.symm)
  intro a ha b hb hk
  have hk' : a.id = b.id ∧ a.adapter = b.adapter ∧ a.model = b.model := by
    simp [key] at hk; exact ⟨hk.1, hk.2.1, hk.2.2⟩
  obtain ⟨hi, hadp, hm⟩ := hk'
  have he : a.enabled = b.enabled := by
    cases hen : c.enable
    · rw [d4f c st r A hen hA a ha, d4g c st r B hen hB b hb]
    · cases hl : c.locked a.adapter
      · have hl' : c.locked b.adapter = false := by rw [← hadp]; exact hl
        obtain ⟨s, hs, hsi, hse⟩ := e6f c st r A hd hen hA a ha hl
        obtain ⟨s', hs', hsi', hse'⟩ := e6g c st r B hd hen hB b hb hl'
        have : s = s' := hd s hs s' hs' (by rw [hsi, hsi', hi])
        subst this
        rw [hse, hse']
      · have hl' : c.locked b.adapter = true := by rw [← hadp]; exact hl
        rw [l5f c st r A hA a ha hl, l5g c st r B hB b hb hl']
  cases a; cases b
  simp_all

end SyncComplete
