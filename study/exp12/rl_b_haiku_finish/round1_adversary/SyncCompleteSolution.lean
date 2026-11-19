import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem adj_id (c : Config) (s : Entry) :
    (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
  unfold adjust
  split <;> simp

theorem adj_en (c : Config) (s : Entry) :
    (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
  rcases c with ⟨lk, ce⟩
  rcases s with ⟨i, a, m, en⟩
  unfold adjust
  cases en <;> cases ce <;> cases hl : lk a <;> simp [hl]

theorem dist (st : List Entry) (s t : Entry) (hd : DistinctIds st)
    (hs : s ∈ st) (ht : t ∈ st) (h : s.id = t.id) : s = t := by
  induction st with
  | nil => simp at hs
  | cons a rest ih =>
    unfold DistinctIds at hd
    rw [List.pairwise_cons] at hd
    obtain ⟨hA, hR⟩ := hd
    rcases List.mem_cons.1 hs with rfl | hs'
    · rcases List.mem_cons.1 ht with rfl | ht'
      · rfl
      · exact absurd h (hA t ht')
    · rcases List.mem_cons.1 ht with rfl | ht'
      · exact absurd h.symm (hA s hs')
      · exact ih hR hs' ht' 

theorem align (c : Config) : ∀ (rest L : List Entry),
    rest.map (fun e => e.id) = L.map (fun e => e.id) →
    (∀ e ∈ rest, ∀ s ∈ L, e.id = s.id → e = adjust c s) →
    rest = L.map (adjust c) := by
  intro rest
  induction rest with
  | nil => intro L h _; cases L with
    | nil => rfl
    | cons _ _ => simp at h
  | cons e rest ih =>
    intro L h hh
    cases L with
    | nil => simp at h
    | cons s L' =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨hh e (by simp) s (by simp) h.1, ih L' h.2 ?_⟩
      intro e' he' s' hs' hid
      exact hh e' (by simp [he']) s' (by simp [hs']) hid

theorem eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = ref c st r := by
  obtain ⟨_, hOL, hNE, _, hRK, hO⟩ := hf
  obtain ⟨rest, hrest⟩ := hRK c st r
  have hmap := hO c st r rest hrest
  have key : rest = (st.filter (absent r)).map (adjust c) := by
    apply align
    · exact hmap
    · intro e he s hs hid
      have hs' := List.mem_filter.1 hs
      have hef : e ∈ f c st r := by rw [hrest]; exact List.mem_append.2 (Or.inr he)
      have hn : e ∉ r := by
        intro hr
        have hh : hasId r s.id = true := by
          unfold hasId
          rw [List.any_eq_true]
          exact ⟨e, hr, by simp [hid]⟩
        have := hs'.2
        unfold absent at this
        simp [hh] at this
      obtain ⟨s', hs'm, _, h1, h2, h3⟩ := hOL c st r e hef hn
      have hss : s' = s := dist st s' s hd hs'm hs'.1 (by rw [← h1]; exact hid)
      subst hss
      have h4 := hNE c st r s' e hd hs'.1 hs'.2 hef hid h2 h3
      rcases e with ⟨i, a, m, en⟩
      have h1' := adj_id c s'
      have h5 := adj_en c s'
      have hx : adjust c s' = ⟨s'.id, s'.adapter, s'.model, s'.enabled && c.enable && !c.locked s'.adapter⟩ := by
        generalize adjust c s' = z at h1' h5 ⊢
        rcases z with ⟨i, a, m, en⟩
        simp only at h1' h5
        rw [h1'.1, h1'.2.1, h1'.2.2, h5]
      rw [hx]
      simp only [Entry.mk.injEq]
      exact ⟨hid, h2, h3, h4⟩
  rw [hrest, key]
  rfl

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [eq_ref f hf c st r hd, eq_ref g hg c st r hd]

end SyncComplete
