import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem sub_filter (p : Entry → Bool) : ∀ (st : List Entry) (l : List Nat),
    List.Sublist l (st.map Entry.id) →
    (∀ x ∈ l, ∃ s ∈ st, s.id = x ∧ p s = true) →
    (∀ s ∈ st, ∀ s' ∈ st, s.id = s'.id → p s = p s') →
    List.Sublist l ((st.filter p).map Entry.id) := by
  intro st
  induction st with
  | nil => intro l h _ _; simpa using h
  | cons s st ih =>
    intro l h hex hc
    have hc' : ∀ a ∈ st, ∀ b ∈ st, a.id = b.id → p a = p b :=
      fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    rw [List.map_cons] at h
    generalize hm : st.map Entry.id = M at h
    cases h with
    | cons _ h' =>
      subst hm
      have hex' : ∀ x ∈ l, ∃ s' ∈ st, s'.id = x ∧ p s' = true := by
        intro x hx
        obtain ⟨s0, hs0, h1, h2⟩ := hex x hx
        rcases List.mem_cons.mp hs0 with rfl | hs0
        · have := h'.subset hx
          obtain ⟨s1, hs1, e1⟩ := List.mem_map.mp this
          refine ⟨s1, hs1, e1, ?_⟩
          have := hc s0 (List.mem_cons_self) s1 (List.mem_cons_of_mem _ hs1) (by rw [h1, e1])
          rw [← this]; exact h2
        · exact ⟨s0, hs0, h1, h2⟩
      have := ih l h' hex' hc'
      simp only [List.filter_cons]
      split
      · exact this.cons _
      · exact this
    | cons_cons _ h' =>
      subst hm
      rename_i l'
      have hps : p s = true := by
        obtain ⟨s0, hs0, h1, h2⟩ := hex s.id (List.mem_cons_self)
        have := hc s0 hs0 s (List.mem_cons_self) h1
        rw [← this]; exact h2
      have hex' : ∀ x ∈ l', ∃ s' ∈ st, s'.id = x ∧ p s' = true := by
        intro x hx
        obtain ⟨s0, hs0, h1, h2⟩ := hex x (List.mem_cons_of_mem _ hx)
        rcases List.mem_cons.mp hs0 with rfl | hs0
        · obtain ⟨s1, hs1, e1⟩ := List.mem_map.mp (h'.subset hx)
          refine ⟨s1, hs1, e1, ?_⟩
          have := hc s0 (List.mem_cons_self) s1 (List.mem_cons_of_mem _ hs1) (by rw [h1, e1])
          rw [← this]; exact h2
        · exact ⟨s0, hs0, h1, h2⟩
      have := ih l' h' hex' hc'
      simp only [List.filter_cons, hps, ite_true, List.map_cons]
      exact this.cons_cons _

theorem build : ∀ (c : Config) (t A : List Entry), t.map Entry.id = A.map Entry.id →
    (∀ e ∈ t, ∀ s ∈ A, e.id = s.id → e = adjust c s) → t = A.map (adjust c) := by
  intro c t
  induction t with
  | nil => intro A h _; cases A with
    | nil => rfl
    | cons a A => simp at h
  | cons e t ih =>
    intro A h hel
    cases A with
    | nil => simp at h
    | cons s A =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨hel e (List.mem_cons_self) s (List.mem_cons_self) h.1, ?_⟩
      exact ih A h.2 (fun e' he' s' hs' => hel e' (List.mem_cons_of_mem _ he') s'
        (List.mem_cons_of_mem _ hs'))

theorem tail_eq (f : SyncImpl) (hp : Passes f) (c : Config) (st r t : List Entry)
    (hd : DistinctIds st) (h : f c st r = r ++ t) :
    t = (st.filter (absent r)).map (adjust c) := by
  obtain ⟨_, _, hOnly, hAll, hNew, hLock, hEn, hOrd, hCnt⟩ := hp
  have hord := hOrd c st r t hd h
  have hlen := hCnt c st r t hd h
  have hsub : List.Sublist (t.map Entry.id) ((st.filter (absent r)).map Entry.id) := by
    apply sub_filter (absent r) st _ hord
    · intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      obtain ⟨s, hs, ha, hid, _, _⟩ := hOnly c st r t hd h e he
      exact ⟨s, hs, hid.symm, ha⟩
    · intro s hs s' hs' hid
      rw [hd s hs s' hs' hid]
  have hids : t.map Entry.id = (st.filter (absent r)).map Entry.id :=
    hsub.eq_of_length (by simp [hlen])
  apply build c t _ hids
  intro e he s hs hid
  obtain ⟨hs, ha⟩ := List.mem_filter.mp hs
  obtain ⟨s2, hs2, ha2, h1, h2, h3⟩ := hOnly c st r t hd h e he
  have : s2 = s := hd s2 hs2 s hs (by rw [← h1, hid])
  subst this
  have hlk := hLock c st r t hd h e he
  have hen := hEn c st r t hd
  have hnw := hNew c st r t hd
  have hu : ∀ _ : c.enable = true, c.locked s2.adapter = false → e.enabled = s2.enabled :=
    fun hc hl => hen hc h e he s2 hs h1.symm hl
  have hl : c.locked s2.adapter = true → e.enabled = false := fun hl => hlk (by rw [h2]; exact hl)
  have hf : c.enable = false → e.enabled = false := fun hc => hnw hc h e he
  cases e with
  | mk i a m en =>
    simp only [] at h1 h2 h3 hl hf hu ⊢
    subst h1 h2 h3
    unfold adjust
    clear he hlk hen hnw hOnly hAll hNew hLock hEn hOrd hCnt hord hlen hids h ha ha2 hs hs2 hd hid
    obtain ⟨i2, a2, m2, en2⟩ := s2
    simp only [] at hl hf hu ⊢
    cases en2 <;> cases hc : c.enable <;> cases hk : c.locked a2 <;>
      simp_all

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨t, ht⟩ := hf.1 c st r hd
  obtain ⟨u, hu⟩ := hg.1 c st r hd
  rw [ht, hu, tail_eq f hf c st r t hd ht, tail_eq g hg c st r u hd hu]

end SyncComplete
