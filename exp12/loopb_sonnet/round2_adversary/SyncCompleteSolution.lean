import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem distinct_eq : ∀ (st : List Entry), DistinctIds st → ∀ s ∈ st, ∀ s' ∈ st,
    s.id = s'.id → s = s' := by
  intro st
  induction st with
  | nil => intro _ s hs; simp at hs
  | cons x t ih =>
    intro hd s hs s' hs' h
    unfold DistinctIds at hd
    rw [List.pairwise_cons] at hd
    obtain ⟨hx, ht⟩ := hd
    simp only [List.mem_cons] at hs hs'
    rcases hs with rfl | hs <;> rcases hs' with rfl | hs'
    · rfl
    · exact absurd h (hx _ hs')
    · exact absurd h.symm (hx _ hs)
    · exact ih ht s hs s' hs' h

theorem sub_eq : ∀ (l l1 l2 : List Nat), l.Nodup → l1.Sublist l → l2.Sublist l →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2 := by
  intro l
  induction l with
  | nil =>
    intro l1 l2 _ h1 h2 _
    have := List.sublist_nil.1 h1
    have := List.sublist_nil.1 h2
    simp_all
  | cons x t ih =>
    intro l1 l2 hn h1 h2 hm
    rw [List.nodup_cons] at hn
    rcases List.sublist_cons_iff.1 h1 with k1 | ⟨a, rfl, k1⟩ <;>
    rcases List.sublist_cons_iff.1 h2 with k2 | ⟨b, rfl, k2⟩
    · exact ih l1 l2 hn.2 k1 k2 hm
    · have : x ∈ l1 := (hm x).2 (by simp)
      exact absurd (k1.subset this) hn.1
    · have : x ∈ l2 := (hm x).1 (by simp)
      exact absurd (k2.subset this) hn.1
    · have : a = b := by
        apply ih a b hn.2 k1 k2
        intro y
        constructor
        · intro hy
          have := (hm y).1 (by simp [hy])
          simp at this
          rcases this with rfl | this
          · exact absurd (k1.subset hy) hn.1
          · exact this
        · intro hy
          have := (hm y).2 (by simp [hy])
          simp at this
          rcases this with rfl | this
          · exact absurd (k2.subset hy) hn.1
          · exact this
      rw [this]

theorem list_eq : ∀ (A B : List Entry), A.map Entry.id = B.map Entry.id →
    (∀ e ∈ A, ∀ e' ∈ B, e.id = e'.id → e = e') → A = B := by
  intro A
  induction A with
  | nil => intro B h _; cases B <;> simp_all
  | cons a t ih =>
    intro B h hp
    cases B with
    | nil => simp at h
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hab := hp a (by simp) b (by simp) h.1
      rw [hab, ih u h.2 (fun e he e' he' => hp e (by simp [he]) e' (by simp [he']))]

theorem main (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) :
    added f c st r = (st.filter (absent r)).map (adjust c) := by
  obtain ⟨_, hOnly, hAll, _, hDis, hLock, hEn, _, hOrd⟩ := hf
  have hid : ∀ s, (adjust c s).id = s.id := by
    intro s; unfold adjust; split <;> simp
  apply list_eq
  · apply sub_eq (st.map Entry.id)
    · exact List.pairwise_map.2 hd
    · exact hOrd c st r
    · rw [List.map_map]
      have h2 : Entry.id ∘ (adjust c) = Entry.id := by
        funext x; exact hid x
      rw [h2]
      exact List.Sublist.map _ List.filter_sublist
    · intro x
      constructor
      · intro hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        obtain ⟨s, hs, ha, h1, _, _⟩ := hOnly c st r e he
        rw [List.map_map]
        refine List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, ?_⟩
        simp only [Function.comp]
        rw [h1, hid]
      · intro hx
        rw [List.map_map] at hx
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
        obtain ⟨hs1, ha⟩ := List.mem_filter.1 hs
        obtain ⟨e, he, h1, _, _⟩ := hAll c st r hd s hs1 ha
        refine List.mem_map.2 ⟨e, he, ?_⟩
        simp only [Function.comp]
        rw [h1, hid]
  · intro e he e' he' hid'
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 he'
    obtain ⟨hs'1, ha'⟩ := List.mem_filter.1 hs'
    obtain ⟨s, hs, ha, h1, h2, h3⟩ := hOnly c st r e he
    have hid2 : s.id = s'.id := by
      rw [← h1, hid', hid]
    have hss := distinct_eq st hd s hs s' hs'1 hid2
    subst hss
    have hfld : (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
      unfold adjust; split <;> simp
    have key : e.enabled = (adjust c s).enabled := by
      cases hc : c.enable <;> cases hlk : c.locked s.adapter
      · have := hDis c st r hc _ he
        simp only [adjust, hc, this]
        split <;> simp_all
      · have := hDis c st r hc _ he
        simp only [adjust, hc, this]
        split <;> simp_all
      · obtain ⟨s2, hs2, _, hi, hen⟩ := hEn c st r hd hc _ he (by rw [h2]; exact hlk)
        have := distinct_eq st hd s2 hs2 s hs (by rw [← hi]; exact h1)
        subst this
        simp [adjust, hc, hlk, hen]
      · have := hLock c st r _ he (by rw [h2]; exact hlk)
        simp only [adjust, hc, hlk, this]
        split <;> simp_all
    obtain ⟨f2, f3⟩ := hfld
    cases e with
    | mk i a m en =>
      simp only at h1 h2 h3 key
      generalize adjust c s = z at *
      cases z
      simp_all

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  have e1 := hf.2.2.2.2.2.2.2.1 c st r
  have e2 := hg.2.2.2.2.2.2.2.1 c st r
  rw [e1, e2, main f hf c st r hd, main g hg c st r hd]

end SyncComplete
