import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem sub_eq : ∀ (L l1 l2 : List Nat), L.Nodup → List.Sublist l1 L → List.Sublist l2 L →
    (∀ x, x ∈ l1 → x ∈ l2) → (∀ x, x ∈ l2 → x ∈ l1) → l1 = l2 := by
  intro L
  induction L with
  | nil =>
    intro l1 l2 _ h1 h2 _ _
    cases h1; cases h2; rfl
  | cons x T ih =>
    intro l1 l2 hn h1 h2 m12 m21
    have hn' := List.nodup_cons.1 hn
    cases h1 with
    | cons _ h1 =>
      cases h2 with
      | cons _ h2 => exact ih l1 l2 hn'.2 h1 h2 m12 m21
      | cons_cons _ h2 =>
        have := m21 x (List.mem_cons_self ..)
        exact absurd (h1.subset this) hn'.1
    | cons_cons _ h1 =>
      cases h2 with
      | cons _ h2 =>
        have := m12 x (List.mem_cons_self ..)
        exact absurd (h2.subset this) hn'.1
      | cons_cons _ h2 =>
        congr 1
        apply ih _ _ hn'.2 h1 h2
        · intro y hy
          rcases List.mem_cons.1 (m12 y (List.mem_cons_of_mem _ hy)) with h | h
          · subst h; exact absurd (h1.subset hy) hn'.1
          · exact h
        · intro y hy
          rcases List.mem_cons.1 (m21 y (List.mem_cons_of_mem _ hy)) with h | h
          · subst h; exact absurd (h2.subset hy) hn'.1
          · exact h

theorem list_eq (c : Config) : ∀ (N A : List Entry), N.map Entry.id = A.map Entry.id →
    (∀ e ∈ N, ∀ s ∈ A, e.id = s.id → e = adjust c s) → N = A.map (adjust c) := by
  intro N
  induction N with
  | nil => intro A h _; cases A <;> simp_all
  | cons e N ih =>
    intro A h hh
    cases A with
    | nil => simp at h
    | cons s A =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨hh e (List.mem_cons_self ..) s (List.mem_cons_self ..) h.1, ?_⟩
      exact ih A h.2 (fun e' he' s' hs' => hh e' (List.mem_cons_of_mem _ he') s'
        (List.mem_cons_of_mem _ hs'))

theorem passes_eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = ref c st r := by
  obtain ⟨_, hend, hadd, honly, _, _, hdis, hen, hlock, hord⟩ := hf
  obtain ⟨N, hN⟩ := hend c st r hd
  have hadded : added f c st r = N := by simp [added, hN]
  have hnodup : (st.map Entry.id).Nodup := by
    have := hd
    unfold DistinctIds at this
    exact List.Pairwise.map _ (fun _ _ h => h) this
  have hidsA : List.Sublist ((st.filter (absent r)).map Entry.id) (st.map Entry.id) :=
    List.Sublist.map _ List.filter_sublist
  have hidsN : List.Sublist (N.map Entry.id) (st.map Entry.id) := by
    have := hord c st r hd; rwa [hadded] at this
  have hids : N.map Entry.id = (st.filter (absent r)).map Entry.id := by
    apply sub_eq _ _ _ hnodup hidsN hidsA
    · intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      have he' : e ∈ added f c st r := by rw [hadded]; exact he
      obtain ⟨s, hs, ha, hid, _⟩ := honly c st r hd e he'
      exact List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, hid.symm⟩
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      obtain ⟨hs, ha⟩ := List.mem_filter.1 hs
      obtain ⟨e, he, hid, _⟩ := hadd c st r hd s hs ha
      rw [hadded] at he
      exact List.mem_map.2 ⟨e, he, hid⟩
  have hNeq : N = (st.filter (absent r)).map (adjust c) := by
    apply list_eq c _ _ hids
    intro e he s hs hid
    have he' : e ∈ added f c st r := by rw [hadded]; exact he
    obtain ⟨hs, ha⟩ := List.mem_filter.1 hs
    obtain ⟨s', hs', _, hid', had', hmod'⟩ := honly c st r hd e he'
    have : s' = s := same_id hd hs' hs (hid'.symm.trans hid)
    subst this
    have hen' : e.enabled = (adjust c s').enabled := by
      unfold adjust
      cases hc : c.enable
      · have := hdis c st r hd hc e he'
        simp [this]
        split <;> simp_all
      · cases hl : c.locked s'.adapter
        · have := hen c st r hd hc s' hs' ha hl e he' hid
          simp [this, hl]
        · have := hlock c st r hd e he' (by rw [had']; exact hl)
          simp [this]
          split <;> simp_all
    have hadj : ∀ x : Entry, (adjust c x).id = x.id ∧ (adjust c x).adapter = x.adapter ∧
        (adjust c x).model = x.model := by
      intro x; unfold adjust; split <;> simp
    obtain ⟨a1, a2, a3⟩ := hadj s'
    generalize adjust c s' = t at *
    cases e; cases t
    simp_all
  show f c st r = r ++ _
  rw [hN, hNeq]

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [passes_eq_ref f hf c st r hd, passes_eq_ref g hg c st r hd]

end SyncComplete
