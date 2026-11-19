import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem sub_eq : ∀ (l : List Nat), l.Nodup → ∀ a b : List Nat, a.Sublist l → b.Sublist l →
    (∀ x, x ∈ a ↔ x ∈ b) → a = b := by
  intro l
  induction l with
  | nil =>
    intro _ a b ha hb _
    have h1 := List.sublist_nil.1 ha
    have h2 := List.sublist_nil.1 hb
    rw [h1, h2]
  | cons x t ih =>
    intro hn a b ha hb hab
    rw [List.nodup_cons] at hn
    rcases List.sublist_cons_iff.1 ha with ha1 | ⟨a', rfl, ha1⟩ <;>
    rcases List.sublist_cons_iff.1 hb with hb1 | ⟨b', rfl, hb1⟩
    · exact ih hn.2 a b ha1 hb1 hab
    · exfalso
      have h3 : x ∈ a := (hab x).2 (by simp)
      exact hn.1 (ha1.subset h3)
    · exfalso
      have h3 : x ∈ b := (hab x).1 (by simp)
      exact hn.1 (hb1.subset h3)
    · congr 1
      apply ih hn.2 a' b' ha1 hb1
      intro y
      constructor
      · intro hy
        have h3 := (hab y).1 (List.mem_cons_of_mem _ hy)
        rcases List.mem_cons.1 h3 with h | h
        · exfalso; rw [h] at hy; exact hn.1 (ha1.subset hy)
        · exact h
      · intro hy
        have h3 := (hab y).2 (List.mem_cons_of_mem _ hy)
        rcases List.mem_cons.1 h3 with h | h
        · exfalso; rw [h] at hy; exact hn.1 (hb1.subset hy)
        · exact h

theorem uniq : ∀ (st : List Entry), DistinctIds st → ∀ s ∈ st, ∀ s' ∈ st, s.id = s'.id → s = s' := by
  intro st
  induction st with
  | nil => intro _ s hs; simp at hs
  | cons x t ih =>
    intro hd s hs s' hs' h
    unfold DistinctIds at hd
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 hs with h1 | h1 <;> rcases List.mem_cons.1 hs' with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd h (hd.1 _ h2)
    · subst h2; exact absurd h.symm (hd.1 _ h1)
    · exact ih hd.2 _ h1 _ h2 h

theorem list_eq (c : Config) : ∀ (A L : List Entry), A.map Entry.id = L.map Entry.id →
    (A.map Entry.id).Nodup →
    (∀ e ∈ A, ∃ s ∈ L, adjust c s = e ∧ s.id = e.id) →
    (∀ s ∈ L, ∀ s' ∈ L, s.id = s'.id → s = s') → A = L.map (adjust c) := by
  intro A
  induction A with
  | nil =>
    intro L h _ _ _
    cases L with
    | nil => rfl
    | cons s L' => simp at h
  | cons e A' ih =>
    intro L h hnd hel hu
    cases L with
    | nil => simp at h
    | cons s L' =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨s', hs', hadj, hid⟩ := hel e (List.mem_cons_self ..)
      have hss : s' = s := by
        apply hu _ hs' _ (List.mem_cons_self ..)
        rw [hid, h1]
      subst hss
      rw [List.map_cons, hadj]
      congr 1
      apply ih L' h2 (by rw [List.map_cons, List.nodup_cons] at hnd; exact hnd.2)
      · intro e' he'
        obtain ⟨s2, hs2, a2, b2⟩ := hel e' (List.mem_cons_of_mem _ he')
        rcases List.mem_cons.1 hs2 with rfl | hs2
        · exfalso
          rw [List.map_cons, List.nodup_cons] at hnd
          exact hnd.1 (List.mem_map.2 ⟨e', he', by rw [← b2, ← hid]⟩)
        · exact ⟨s2, hs2, a2, b2⟩
      · intro x hx y hy
        exact hu x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)

theorem added_eq (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : added f c st r = (st.filter (absent r)).map (adjust c) := by
  obtain ⟨_, hOnly, hAll, _, hDis, hLock, hEnable, _, hOrd⟩ := hf
  have hnd : (st.map Entry.id).Nodup := by
    unfold List.Nodup
    exact List.pairwise_map.2 hd
  have hel : ∀ e ∈ added f c st r,
      ∃ s ∈ st.filter (absent r), adjust c s = e ∧ s.id = e.id := by
    intro e he
    obtain ⟨s, hs, hab, h1, h2, h3⟩ := hOnly c st r e he
    refine ⟨s, List.mem_filter.2 ⟨hs, hab⟩, ?_, h1.symm⟩
    have hen : (adjust c s).enabled = e.enabled := by
      unfold adjust
      cases hc : c.enable
      · have := hDis c st r hc e he
        by_cases hse : s.enabled <;> simp [hse, this]
      · cases hl : c.locked s.adapter
        · have hl' : c.locked e.adapter = false := by rw [h2]; exact hl
          obtain ⟨s'', hs'', _, h1'', h2''⟩ := hEnable c st r hd hc e he hl'
          have : s'' = s := uniq st hd _ hs'' _ hs (by rw [← h1'', h1])
          subst this
          simp [hl, h2'']
        · have hl' : c.locked e.adapter = true := by rw [h2]; exact hl
          have := hLock c st r e he hl'
          by_cases hse : s.enabled <;> simp [hse, this, hl]
    have hshape : adjust c s = Entry.mk s.id s.adapter s.model (adjust c s).enabled := by
      unfold adjust
      split <;> simp
    rw [hshape, hen]
    cases e
    simp_all
  have hmap : (added f c st r).map Entry.id = (st.filter (absent r)).map Entry.id := by
    apply sub_eq _ hnd _ _ (hOrd c st r)
    · exact (List.filter_sublist).map _
    · intro x
      constructor
      · intro hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        obtain ⟨s, hs, _, hid⟩ := hel e he
        exact List.mem_map.2 ⟨s, hs, hid⟩
      · intro hx
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
        obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs
        obtain ⟨e, he, h1, _⟩ := hAll c st r hd s hs1 hs2
        exact List.mem_map.2 ⟨e, he, h1⟩
  apply list_eq c _ _ hmap
  · rw [hmap]
    exact hnd.sublist ((List.filter_sublist).map _)
  · exact hel
  · intro s hs s' hs' h
    exact uniq st hd s (List.mem_filter.1 hs).1 s' (List.mem_filter.1 hs').1 h

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  have hfe := hf.2.2.2.2.2.2.2.1 c st r
  have hge := hg.2.2.2.2.2.2.2.1 c st r
  rw [hfe, hge, added_eq f hf c st r hd, added_eq g hg c st r hd]

end SyncComplete
