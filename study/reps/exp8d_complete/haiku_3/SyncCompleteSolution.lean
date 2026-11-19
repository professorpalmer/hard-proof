import SyncLaws

open SyncLaws

namespace SyncComplete

/-- Two rows with one key have one `enabled` value, when both designs pass the
laws. Laws 4 and 5 fix the value when `--enable` is off or the adapter is locked.
Law 6 ties the value to the starter entry with that id, and distinct ids make
that entry the same for both designs. -/
theorem enabled_eq (f g : SyncImpl) (hf : Passes f) (hg : Passes g)
    (c : Config) (st r : List Entry) (hd : DistinctIds st)
    (af ag : List Entry) (hF : f c st r = r ++ af) (hG : g c st r = r ++ ag)
    (a b : Entry) (ha : a ∈ af) (hb : b ∈ ag) (hk : key a = key b) :
    a.enabled = b.enabled := by
  have hkey : a.id = b.id ∧ a.adapter = b.adapter ∧ a.model = b.model := by
    simpa [key] using hk
  obtain ⟨hid, had, _⟩ := hkey
  by_cases hen : c.enable = true
  · by_cases hl : c.locked a.adapter = true
    · have h1 : a.enabled = false := hf.2.2.2.2.1 c st r af hF a ha hl
      have hlb : c.locked b.adapter = true := by
        rw [← had]; exact hl
      have h2 : b.enabled = false := hg.2.2.2.2.1 c st r ag hG b hb hlb
      rw [h1, h2]
    · have hu : c.locked a.adapter = false := by simpa using hl
      have hub : c.locked b.adapter = false := by
        rw [← had]; exact hu
      obtain ⟨s, hs, hsid, hsen⟩ := hf.2.2.2.2.2.1 c st r af hd hen hF a ha hu
      obtain ⟨t, ht, htid, hten⟩ := hg.2.2.2.2.2.1 c st r ag hd hen hG b hb hub
      have hst : s = t := hd s hs t ht (hsid.trans (hid.trans htid.symm))
      rw [hsen, hten, hst]
  · have hf' : c.enable = false := by simpa using hen
    rw [hf.2.2.2.1 c st r af hf' hF a ha, hg.2.2.2.1 c st r ag hf' hG b hb]

/-- Two lists of rows with the same keys in the same order are equal, when
paired rows with one key have one `enabled` value. -/
theorem list_eq_of_keys : ∀ (A B : List Entry), A.map key = B.map key →
    (∀ a ∈ A, ∀ b ∈ B, key a = key b → a.enabled = b.enabled) → A = B
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: A', b :: B', h, he => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hen : a.enabled = b.enabled :=
      he a (List.mem_cons_self) b (List.mem_cons_self) h.1
    have hrest : A' = B' :=
      list_eq_of_keys A' B' h.2
        (fun a' ha' b' hb' hk => he a' (List.mem_cons_of_mem _ ha') b'
          (List.mem_cons_of_mem _ hb') hk)
    have hab : a = b := by
      obtain ⟨i1, a1, m1, e1⟩ := a
      obtain ⟨i2, a2, m2, e2⟩ := b
      have hk : (i1, a1, m1) = (i2, a2, m2) := h.1
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      dsimp only at hen
      subst hen
      rfl
    rw [hab, hrest]

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨af, hF⟩ := hf.1 c st r
  obtain ⟨ag, hG⟩ := hg.1 c st r
  have hkeys : af.map key = ag.map key := by
    rw [hf.2.2.2.2.2.2.2 c st r af hF, hg.2.2.2.2.2.2.2 c st r ag hG]
  have hA : af = ag :=
    list_eq_of_keys af ag hkeys
      (fun a ha b hb hk => enabled_eq f g hf hg c st r hd af ag hF hG a b ha hb hk)
  rw [hF, hG, hA]

end SyncComplete
