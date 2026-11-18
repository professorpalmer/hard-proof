import Types
import Ref
import Laws

open HP

namespace HPComplete

theorem distinct_eq : ∀ (st : List Entry), (st.map Entry.id).Nodup → ∀ s ∈ st, ∀ s' ∈ st,
    s.id = s'.id → s = s' := by
  intro st
  induction st with
  | nil => intro _ s hs; simp at hs
  | cons x t ih =>
    intro hd s hs s' hs' h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    obtain ⟨hx, ht⟩ := hd
    simp only [List.mem_cons] at hs hs'
    rcases hs with rfl | hs <;> rcases hs' with rfl | hs'
    · rfl
    · exact absurd ⟨s', hs', h.symm⟩ hx
    · exact absurd ⟨s, hs, h⟩ hx
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

theorem main (f : Impl) (hf : Passes f) (x : Input) (hl : Legal x) :
    added f x = (x.starter.filter (absent x.registry)).map (adjust x) := by
  obtain ⟨_, hOnly, hAll, _, hDis, hLock, hEn, hOrd⟩ := hf
  have hd : (x.starter.map Entry.id).Nodup := of_decide_eq_true hl
  have hid : ∀ s, (adjust x s).id = s.id := by
    intro s; unfold adjust; split <;> simp
  apply list_eq
  · apply sub_eq (x.starter.map Entry.id)
    · exact hd
    · exact hOrd x
    · rw [List.map_map]
      have h2 : Entry.id ∘ (adjust x) = Entry.id := by
        funext y; exact hid y
      rw [h2]
      exact List.Sublist.map _ List.filter_sublist
    · intro i
      constructor
      · intro hi
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
        obtain ⟨s, hs, ha, h1, _, _⟩ := hOnly x e he
        rw [List.map_map]
        refine List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, ?_⟩
        simp only [Function.comp]
        rw [h1, hid]
      · intro hi
        rw [List.map_map] at hi
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hi
        obtain ⟨hs1, ha⟩ := List.mem_filter.1 hs
        obtain ⟨e, he, h1, _, _⟩ := hAll x hl s hs1 ha
        refine List.mem_map.2 ⟨e, he, ?_⟩
        simp only [Function.comp]
        rw [h1, hid]
  · intro e he e' he' hid'
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 he'
    obtain ⟨hs'1, ha'⟩ := List.mem_filter.1 hs'
    obtain ⟨s, hs, ha, h1, h2, h3⟩ := hOnly x e he
    have hid2 : s.id = s'.id := by
      rw [← h1, hid', hid]
    have hss := distinct_eq x.starter hd s hs s' hs'1 hid2
    subst hss
    have hfld : (adjust x s).adapter = s.adapter ∧ (adjust x s).model = s.model := by
      unfold adjust; split <;> simp
    have key : e.enabled = (adjust x s).enabled := by
      cases hc : x.enable <;> cases hlk : isLocked x s.adapter
      · have := hDis x hc _ he
        simp only [adjust, hc, this]
        split <;> simp_all
      · have := hDis x hc _ he
        simp only [adjust, hc, this]
        split <;> simp_all
      · obtain ⟨s2, hs2, _, hi, hen⟩ := hEn x hl hc _ he (by rw [h2]; exact hlk)
        have := distinct_eq x.starter hd s2 hs2 s hs (by rw [← hi]; exact h1)
        subst this
        simp [adjust, hc, hlk, hen]
      · have := hLock x _ he (by rw [h2]; exact hlk)
        simp only [adjust, hc, hlk, this]
        split <;> simp_all
    obtain ⟨f2, f3⟩ := hfld
    cases e with
    | mk i a m en =>
      simp only at h1 h2 h3 key
      generalize adjust x s = z at *
      cases z
      simp_all

theorem split_added (f : Impl) (hf : Passes f) (x : Input) : f x = x.registry ++ added f x := by
  exact (List.prefix_iff_eq_append.1 (hf.1 x)).symm

theorem laws_complete : ∀ f g : Impl, Passes f → Passes g →
    ∀ x : Input, Legal x → f x = g x := by
  intro f g hf hg x hl
  rw [split_added f hf x, split_added g hg x, main f hf x hl, main g hg x hl]

end HPComplete
