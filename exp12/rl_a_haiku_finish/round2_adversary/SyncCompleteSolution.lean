import Sync
import SyncLaws

open Sync

namespace SyncComplete

private theorem list_eq_of_ids : ∀ (l1 l2 : List Entry), l1.map Entry.id = l2.map Entry.id →
    (∀ e ∈ l1, ∀ e' ∈ l2, e.id = e'.id → e = e') → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l1, b :: l2, h, hy => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab : a = b := hy a (by simp) b (by simp) h.1
    subst hab
    have := list_eq_of_ids l1 l2 h.2 (fun e he e' he' hi => hy e (by simp [he]) e' (by simp [he']) hi)
    rw [this]

private theorem adj_enabled (c : Config) (s : Entry) :
    (adjust c s).enabled = (c.enable && !c.locked s.adapter && s.enabled) := by
  cases hs : s.enabled <;> cases hc : c.enable <;> cases hl : c.locked s.adapter <;>
    simp [adjust, hs, hc, hl]

private theorem adj_id (c : Config) (s : Entry) : (adjust c s).id = s.id := by
  unfold adjust; split <;> rfl
private theorem adj_ad (c : Config) (s : Entry) : (adjust c s).adapter = s.adapter := by
  unfold adjust; split <;> rfl
private theorem adj_md (c : Config) (s : Entry) : (adjust c s).model = s.model := by
  unfold adjust; split <;> rfl

private theorem eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = ref c st r := by
  obtain ⟨_, hEnd, _, _, _, hEn, _, hMult⟩ := hf
  obtain ⟨tail, ht⟩ := hEnd c st r
  show f c st r = r ++ (st.filter (absent r)).map (adjust c)
  rw [ht]
  congr 1
  apply list_eq_of_ids
  · rw [hMult c st r tail ht, List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext (adj_id c)
    rw [this]
  · intro e he e' he' hi
    obtain ⟨s, hs, hid, had, hmd, hen⟩ := hEn c st r tail ht e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he'
    obtain ⟨has, _⟩ := List.mem_filter.mp ha
    rw [adj_id] at hi
    have : s = a := hd s hs a has (by rw [← hid, hi])
    subst this
    have h2 := adj_enabled c s
    have i2 := adj_id c s
    have a2 := adj_ad c s
    have m2 := adj_md c s
    revert hid had hmd hen
    cases e
    cases hh : adjust c s
    simp only [hh] at h2 i2 a2 m2
    simp only [Entry.mk.injEq]
    intro hid had hmd hen
    exact ⟨hid.trans i2.symm, had.trans a2.symm, hmd.trans m2.symm, hen.trans h2.symm⟩

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [eq_ref f hf c st r hd, eq_ref g hg c st r hd]

end SyncComplete
