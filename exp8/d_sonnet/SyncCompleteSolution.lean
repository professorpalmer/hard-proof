import SyncLaws

open SyncLaws

namespace SyncComplete

theorem build_eq (c : Config) :
    ∀ (added L : List Entry), added.map key = L.map key →
    (∀ a ∈ added, ∀ s ∈ L, key a = key s → a = adjust c s) →
    added = L.map (adjust c)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, s :: ls, h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨hp a (by simp) s (by simp) h.1, ?_⟩
    exact build_eq c as ls h.2 (fun a' ha' s' hs' hk =>
      hp a' (List.mem_cons_of_mem _ ha') s' (List.mem_cons_of_mem _ hs') hk)

theorem eq_ref (f : SyncImpl) (hf : Passes f) (c : Config) (st r : List Entry)
    (hd : DistinctIds st) : f c st r = refSync c st r := by
  obtain ⟨h1, _, _, h4, h5, h6, _, h8⟩ := hf
  obtain ⟨added, hadd⟩ := h1 c st r
  have hk := h8 c st r added hadd
  have : added = (st.filter (absent r)).map (adjust c) := by
    apply build_eq c added _ hk
    intro a ha s hs hka
    have hsst : s ∈ st := (List.mem_filter.mp hs).1
    simp only [key, Prod.mk.injEq] at hka
    obtain ⟨hi, hadp, hm⟩ := hka
    by_cases he : c.enable = true
    · by_cases hl : c.locked a.adapter = true
      · have e5 := h5 c st r added hadd a ha hl
        have hls : c.locked s.adapter = true := by rw [← hadp]; exact hl
        cases a; cases s
        simp_all [adjust]
      · have hl' : c.locked a.adapter = false := by simpa using hl
        obtain ⟨s', hs', hid, hen⟩ := h6 c st r added hd he hadd a ha hl'
        have hss : s' = s := hd s' hs' s hsst (by rw [hid, hi])
        subst hss
        have hls : c.locked s'.adapter = false := by rw [← hadp]; exact hl'
        have : a = { a with enabled := s'.enabled } := by cases a; simp_all
        simp [adjust, hls, he]
        cases a; cases s'; simp_all
    · have hf' : c.enable = false := by simpa using he
      have e4 := h4 c st r added hf' hadd a ha
      simp [adjust, hf']
      cases a; cases s; simp_all
  rw [hadd, this]; rfl

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  rw [eq_ref f hf c st r hd, eq_ref g hg c st r hd]

end SyncComplete
