import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem hid (c : Config) (s : Entry) :
    (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
  unfold adjust
  split <;> simp

theorem hen (c : Config) (s : Entry) :
    (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
  rcases c with ⟨lk, ce⟩
  rcases s with ⟨i, a, m, en⟩
  unfold adjust
  cases en <;> cases ce <;> cases hl : lk a <;> simp [hl]

theorem hdistinct : ∀ (st : List Entry) (s t : Entry), DistinctIds st →
    s ∈ st → t ∈ st → s.id = t.id → s = t := by
  intro st
  induction st with
  | nil => intro s t _ hs; simp at hs
  | cons a rest ih =>
    intro s t hd hs ht hst
    unfold DistinctIds at hd
    rw [List.pairwise_cons] at hd
    obtain ⟨hA, hR⟩ := hd
    rcases List.mem_cons.1 hs with rfl | hs'
    · rcases List.mem_cons.1 ht with rfl | ht'
      · rfl
      · exact absurd hst (hA t ht')
    · rcases List.mem_cons.1 ht with rfl | ht'
      · exact absurd hst.symm (hA s hs')
      · exact ih s t hR hs' ht' hst

theorem list_eq : ∀ (l1 l2 : List Entry), l1.map (fun e => e.id) = l2.map (fun e => e.id) →
    (∀ e ∈ l1, ∀ e' ∈ l2, e.id = e'.id → e = e') → l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h _; cases l2 with
    | nil => rfl
    | cons b t => simp at h
  | cons a t ih =>
    intro l2 h hp
    cases l2 with
    | nil => simp at h
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hab : a = b := hp a (by simp) b (by simp) h.1
      subst hab
      have := ih u h.2 (fun e he e' he' => hp e (by simp [he]) e' (by simp [he']))
      rw [this]

theorem uniq (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = r ++ (st.filter (absent r)).map (adjust c) := by
  obtain ⟨_, hO, hN, _, hR, hS⟩ := hf
  obtain ⟨rest, hrest⟩ := hR c st r
  have ids := hS c st r rest hrest
  rw [hrest]
  congr 1
  apply list_eq
  · rw [ids, List.map_map]
    simp [Function.comp_def, fun s => (hid c s).1]
  · intro e he e' he' hee
    have hef : e ∈ f c st r := by rw [hrest]; exact List.mem_append_right _ he
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 he'
    obtain ⟨hs'st, hs'abs⟩ := List.mem_filter.1 hs'
    -- e not in r
    have hmemids : e.id ∈ (st.filter (absent r)).map (fun e => e.id) := by
      rw [← ids]; exact List.mem_map.2 ⟨e, he, rfl⟩
    obtain ⟨s0, hs0, hs0id⟩ := List.mem_map.1 hmemids
    obtain ⟨_, hs0abs⟩ := List.mem_filter.1 hs0
    have hnr : e ∉ r := by
      intro hr
      have hh : hasId r s0.id = true := by
        unfold hasId
        rw [List.any_eq_true]
        exact ⟨e, hr, by simp [hs0id]⟩
      unfold absent at hs0abs
      simp [hh] at hs0abs
    obtain ⟨s, hs, ha, h1, h2, h3⟩ := hO c st r e hef hnr
    have hss : s = s' := by
      apply hdistinct st s s' hd hs hs'st
      rw [← h1, hee, (hid c s').1]
    subst hss
    have hE := hN c st r s e hd hs ha hef h1 h2 h3
    rcases e with ⟨i, a, m, en⟩
    have a1 := (hid c s).1
    have a2 := (hid c s).2.1
    have a3 := (hid c s).2.2
    have a4 := hen c s
    simp only at h1 h2 h3 hE
    rcases hadj : adjust c s with ⟨i', a', m', en'⟩
    rw [hadj] at a1 a2 a3 a4
    simp only at a1 a2 a3 a4
    simp [h1, h2, h3, hE, a1, a2, a3, a4]

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [uniq f hf c st r hd, uniq g hg c st r hd]

end SyncComplete
