import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem adjust_enabled' (c : Config) (s : Entry) :
    (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
  unfold adjust
  cases h1 : s.enabled <;> cases c.enable <;> cases c.locked s.adapter <;> simp [h1]

theorem adjust_fields (c : Config) (s : Entry) :
    (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧
    (adjust c s).model = s.model := by
  unfold adjust; split <;> simp

theorem entry_ext {a b : Entry} (h1 : a.id = b.id) (h2 : a.adapter = b.adapter)
    (h3 : a.model = b.model) (h4 : a.enabled = b.enabled) : a = b := by
  cases a; cases b; simp_all

theorem key (f : SyncImpl) (hp : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) :
    added f c st r = (st.filter (absent r)).map (adjust c) := by
  obtain ⟨_, _, hEach, hOnly, hOnce, _, hDis, hEn, hLock, hOrd⟩ := hp
  have hsame := @same_id st hd
  have hrow : ∀ e ∈ added f c st r, ∃ s ∈ st.filter (absent r),
      e = adjust c s ∧ s.id = e.id := by
    intro e he
    obtain ⟨s, hs, ha, hi, hA, hM⟩ := hOnly c st r hd e he
    refine ⟨s, List.mem_filter.2 ⟨hs, ha⟩, ?_, hi.symm⟩
    have hen : e.enabled = (adjust c s).enabled := by
      rw [adjust_enabled']
      cases hc : c.enable
      · have := hDis c st r hd hc e he
        simp [this]
      · cases hl : c.locked s.adapter
        · have := hEn c st r hd hc s hs ha hl e he hi
          simp [this]
        · have := hLock c st r hd e he (by rw [hA]; exact hl)
          simp [this]
    obtain ⟨f1, f2, f3⟩ := adjust_fields c s
    exact entry_ext (by rw [f1, hi]) (by rw [f2, hA]) (by rw [f3, hM]) hen
  have hlen := hOnce c st r hd
  -- ids
  have hfm : ∀ s ∈ st, absent r s = decide (s.id ∈ (st.filter (absent r)).map (·.id)) := by
    intro s hs
    cases ha : absent r s
    · apply Eq.symm
      rw [decide_eq_false_iff_not]
      intro hm
      obtain ⟨t, ht, hti⟩ := List.mem_map.1 hm
      obtain ⟨ht1, ht2⟩ := List.mem_filter.1 ht
      have := hsame hs ht1 hti.symm
      subst this; simp_all
    · apply Eq.symm
      rw [decide_eq_true_eq]
      exact List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, rfl⟩
  have hF : (st.filter (absent r)).map (·.id)
      = (st.map (·.id)).filter (fun i => decide (i ∈ (st.filter (absent r)).map (·.id))) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro s hs; exact hfm s hs
  have hsub : List.Sublist ((added f c st r).map (·.id)) ((st.filter (absent r)).map (·.id)) := by
    have h1 := hOrd c st r hd
    have h2 := h1.filter (fun i => decide (i ∈ (st.filter (absent r)).map (·.id)))
    rw [← hF] at h2
    have h3 : ((added f c st r).map (·.id)).filter
        (fun i => decide (i ∈ (st.filter (absent r)).map (·.id)))
        = (added f c st r).map (·.id) := by
      apply List.filter_eq_self.2
      intro i hi
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
      obtain ⟨s, hs, _, hsi⟩ := hrow e he
      simpa using List.mem_map.2 ⟨s, hs, hsi⟩
    rwa [h3] at h2
  have hids : (added f c st r).map (·.id) = (st.filter (absent r)).map (·.id) := by
    apply hsub.eq_of_length
    simp [hlen]
  apply List.ext_getElem
  · simpa using hlen
  · intro i h1 h2
    have hl : i < (st.filter (absent r)).length := by simpa [hlen] using h1
    have hid : ((added f c st r)[i]'h1).id = ((st.filter (absent r))[i]'hl).id := by
      have := List.getElem_of_eq hids (by simpa using h1)
      simpa using this
    obtain ⟨s, hs, he, hsi⟩ := hrow _ (List.getElem_mem h1)
    have hmem := List.getElem_mem hl
    have : s = (st.filter (absent r))[i] :=
      hsame (List.mem_filter.1 hs).1 (List.mem_filter.1 hmem).1 (by rw [hsi, hid])
    simp [he, this]

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  have e1 := key f hf c st r hd
  have e2 := key g hg c st r hd
  obtain ⟨_, hNf, _⟩ := hf
  obtain ⟨_, hNg, _⟩ := hg
  obtain ⟨n, hn⟩ := hNf c st r hd
  obtain ⟨m, hm⟩ := hNg c st r hd
  have a1 : added f c st r = n := by simp [added, hn]
  have a2 : added g c st r = m := by simp [added, hm]
  rw [hn, hm, ← a1, ← a2, e1, e2]

end SyncComplete
