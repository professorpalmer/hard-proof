import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem zip_eq : ∀ (t L : List Entry) (c : Config),
    t.map (·.id) = L.map (·.id) →
    (∀ e ∈ t, ∀ s ∈ L, e.id = s.id → e = adjust c s) →
    t = L.map (adjust c)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | e :: t, s :: L, c, h, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h
    have h1 := h2 e (by simp) s (by simp) h.1
    have := zip_eq t L c h.2 (fun e' he' s' hs' hi => h2 e' (by simp [he']) s' (by simp [hs']) hi)
    simp [h1, this]

theorem key (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = ref c st r := by
  obtain ⟨hP, _, hO, hA, hND, hLD, hEK, hSO, hOne⟩ := hf
  obtain ⟨t, ht⟩ := hP c st r hd
  have hlen := hOne c st r t ht
  have hsub := hSO c st r t hd ht
  have hOO := hO c st r t hd ht
  obtain ⟨l, hl, hlt⟩ := List.sublist_map_iff.mp hsub
  have hlall : ∀ x ∈ l, absent r x = true := by
    intro x hx
    have hxs : x ∈ st := hl.subset hx
    have : x.id ∈ t.map (·.id) := by rw [hlt]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨e, het, hei⟩ := List.mem_map.mp this
    obtain ⟨s, hs, ha, hid, _⟩ := hOO e het
    have : s = x := hd s hs x hxs (by rw [← hid]; exact hei)
    rw [← this]; exact ha
  have hlL : l.Sublist (st.filter (absent r)) := by
    have := hl.filter (absent r)
    rwa [List.filter_eq_self.mpr hlall] at this
  have hll : l.length = (st.filter (absent r)).length := by
    have := congrArg List.length hlt
    simp at this
    omega
  have hleq : l = st.filter (absent r) := hlL.eq_of_length hll
  have hids : t.map (·.id) = (st.filter (absent r)).map (·.id) := by rw [hlt, hleq]
  unfold ref
  rw [ht]
  congr 1
  apply zip_eq t _ c hids
  intro e he s hs hid
  obtain ⟨hsst, hsa⟩ := List.mem_filter.mp hs
  obtain ⟨s0, hs0, _, h0id, h0a, h0m⟩ := hOO e he
  have : s0 = s := hd s0 hs0 s hsst (by rw [← h0id]; exact hid)
  subst this
  have hLD' := hLD c st r t hd ht e he
  have hND' := hND c st r t hd
  have hEK' := hEK c st r t hd
  have key2 : e.enabled = (adjust c s0).enabled := by
    cases hc : c.enable
    · have h1 := hND' hc ht e he
      unfold adjust
      cases hs : s0.enabled <;> simp [hs, hc, h1]
    · cases hl : c.locked s0.adapter
      · have h1 := hEK' hc ht e he s0 hsst h0id.symm hl
        unfold adjust
        cases hs : s0.enabled <;> simp [hs, hc, hl, h1]
      · have h1 := hLD' (by rw [h0a]; exact hl)
        unfold adjust
        cases hs : s0.enabled <;> simp [hs, hc, hl, h1]
  have hadj_id : (adjust c s0).id = s0.id := by unfold adjust; split <;> rfl
  have hadj_ad : (adjust c s0).adapter = s0.adapter := by unfold adjust; split <;> rfl
  have hadj_m : (adjust c s0).model = s0.model := by unfold adjust; split <;> rfl
  cases e
  cases hh : adjust c s0
  simp only [hh] at hadj_id hadj_ad hadj_m key2
  simp_all

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [key f hf c st r hd, key g hg c st r hd]

end SyncComplete
