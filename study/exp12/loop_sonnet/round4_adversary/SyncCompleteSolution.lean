import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem list_eq {l1 l2 : List Entry} (hid : l1.map Entry.id = l2.map Entry.id)
    (hp : ∀ x ∈ l1, ∀ y ∈ l2, x.id = y.id → x = y) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a l ih =>
    cases l2 with
    | nil => simp at hid
    | cons b l2 =>
      simp only [List.map_cons, List.cons.injEq] at hid
      have hab : a = b := hp a (by simp) b (by simp) hid.1
      subst hab
      congr 1
      exact ih hid.2 (fun x hx y hy => hp x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  have key : ∀ (f : SyncImpl), Passes f → ∀ (c : Config) (st r : List Entry), DistinctIds st →
      f c st r = ref c st r := by
    intro f hf c st r hd
    obtain ⟨hK, hO, hA, hI, hD, hE, hL, hS, hN, hLen⟩ := hf
    obtain ⟨new, hnew⟩ := hK c st r hd
    have adj_id : ∀ s, (adjust c s).id = s.id := by
      intro s; simp [adjust]; split <;> simp
    have hlen := hLen c st r hd
    rw [hnew] at hlen
    simp only [List.length_append] at hlen
    have hsub := hS c st r hd new hnew
    -- every new row is not in r
    have hnotr : ∀ x ∈ new, x ∉ r := by
      intro x hx hxr
      have hid : hasId r x.id = true := by
        simp only [hasId, List.any_eq_true, beq_iff_eq]
        exact ⟨x, hxr, rfl⟩
      have h := hN c st r hd x.id hid
      rw [hnew, List.countP_append] at h
      have h0 : new.countP (fun e => e.id == x.id) = 0 := by omega
      rw [List.countP_eq_zero] at h0
      have := h0 x hx
      simp at this
    have hx_abs : ∀ x ∈ new, ∃ s ∈ st, absent r s = true ∧ x.id = s.id ∧ x.adapter = s.adapter
        ∧ x.model = s.model := by
      intro x hx
      exact hO c st r hd x (by rw [hnew]; exact List.mem_append_right _ hx) (hnotr x hx)
    have hlenA : (new.map Entry.id).length = ((st.filter (absent r)).map Entry.id).length := by
      simp only [List.length_map]; omega
    let p : Nat → Bool := fun i => decide (i ∈ (st.filter (absent r)).map Entry.id)
    have hnewp : ∀ i ∈ new.map Entry.id, p i = true := by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
      obtain ⟨s, hs, ha, hid, _⟩ := hx_abs x hx
      simp only [p, decide_eq_true_eq]
      exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, hid.symm⟩
    have hfilt : (st.map Entry.id).filter p = (st.filter (absent r)).map Entry.id := by
      rw [List.filter_map]
      have : st.filter (p ∘ Entry.id) = st.filter (absent r) := by
        apply List.filter_congr
        intro s hs
        simp only [Function.comp, p]
        rw [Bool.eq_iff_iff, decide_eq_true_eq]
        constructor
        · intro h
          obtain ⟨s', hs', hid⟩ := List.mem_map.mp h
          obtain ⟨hs'1, hs'2⟩ := List.mem_filter.mp hs'
          have : s' = s := hd s' hs'1 s hs hid
          subst this
          exact hs'2
        · intro h
          exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, h⟩, rfl⟩
      rw [this]
    have hl1 : List.Sublist (new.map Entry.id) ((st.map Entry.id).filter p) := by
      have := hsub.filter p
      rwa [List.filter_eq_self.mpr hnewp] at this
    rw [hfilt] at hl1
    have hids : new.map Entry.id = (st.filter (absent r)).map Entry.id :=
      hl1.eq_of_length hlenA
    have hnew' : new = (st.filter (absent r)).map (adjust c) := by
      apply list_eq
      · rw [hids, List.map_map]
        simp [Function.comp_def, adj_id]
      · intro x hx y hy hxy
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
        obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
        obtain ⟨s', hs', ha', hid', had', hm'⟩ := hx_abs x hx
        rw [adj_id] at hxy
        have : s' = s := hd s' hs' s hs1 (by rw [← hid', hxy])
        subst this
        have hxm : x ∈ f c st r := by rw [hnew]; exact List.mem_append_right _ hx
        have hen : x.enabled = (adjust c s').enabled := by
          by_cases h1 : c.enable = true
          · by_cases h2 : c.locked s'.adapter = true
            · have := hL c st r hd s' hs1 hs2 h2 x hxm hid'
              simp only [adjust, h1, h2]; cases hh : s'.enabled <;> simp [this, hh]
            · have h2' : c.locked s'.adapter = false := by simpa using h2
              have := hE c st r hd h1 s' hs1 hs2 h2' x hxm hid'
              simp only [adjust, h1, h2']; simp [this]
          · have h1' : c.enable = false := by simpa using h1
            have := hD c st r hd h1' s' hs1 hs2 x hxm hid'
            simp only [adjust, h1']; cases hh : s'.enabled <;> simp [this, hh]
        have ha2 : (adjust c s').adapter = s'.adapter := by simp [adjust]; split <;> simp
        have hm2 : (adjust c s').model = s'.model := by simp [adjust]; split <;> simp
        have hi2 : (adjust c s').id = s'.id := adj_id s'
        generalize adjust c s' = y at *
        cases x; cases y
        simp_all
    rw [hnew, hnew']
    rfl
  intro f g hf hg c st r hd
  rw [key f hf c st r hd, key g hg c st r hd]

end SyncComplete
