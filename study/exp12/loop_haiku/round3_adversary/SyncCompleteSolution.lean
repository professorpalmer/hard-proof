import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem tail_eq (f : SyncImpl) (hf : Passes f) (c : Config) (st r tail : List Entry)
    (hd : DistinctIds st) (h : f c st r = r ++ tail) :
    tail = (st.filter (absent r)).map (adjust c) := by
  obtain ⟨_, _, hOnly, hEvery, _, hEn, hOrd, hOne⟩ := hf
  have hid : ∀ c s, (adjust c s).id = s.id := by
    intro c s; unfold adjust; split <;> rfl
  have had : ∀ c s, (adjust c s).adapter = s.adapter := by
    intro c s; unfold adjust; split <;> rfl
  have hmd : ∀ c s, (adjust c s).model = s.model := by
    intro c s; unfold adjust; split <;> rfl
  have hen : ∀ c s, (adjust c s).enabled = (c.enable && !c.locked s.adapter && s.enabled) := by
    intro c s
    cases hs : s.enabled <;> cases hc : c.enable <;> cases hl : c.locked s.adapter <;>
      simp [adjust, hs, hc, hl]
  have helem : ∀ e ∈ tail, ∃ a ∈ st.filter (absent r), e = adjust c a := by
    intro e he
    obtain ⟨s, hs, h1, h2, h3, h4⟩ := hEn c st r tail h e he
    obtain ⟨s', hs', hab, h1', h2', h3'⟩ := hOnly c st r tail h e he
    have : s = s' := hd s hs s' hs' (h1.symm.trans h1')
    subst this
    refine ⟨s, List.mem_filter.mpr ⟨hs, hab⟩, ?_⟩
    have ext : ∀ x y : Entry, x.id = y.id → x.adapter = y.adapter → x.model = y.model →
        x.enabled = y.enabled → x = y := by
      intro x y h1 h2 h3 h4
      cases x; cases y; simp_all
    exact ext _ _ (by rw [hid]; exact h1) (by rw [had]; exact h2)
      (by rw [hmd]; exact h3) (by rw [hen]; exact h4)
  let q : Nat → Bool := fun i => st.any (fun s => s.id == i && absent r s)
  have hq : ∀ s ∈ st, q s.id = absent r s := by
    intro s hs
    simp only [q]
    cases hab : absent r s
    · simp only [Bool.eq_false_iff, ne_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      rintro ⟨s', hs', h1, h2⟩
      have := hd s' hs' s hs h1
      subst this
      rw [hab] at h2; exact absurd h2 (by decide)
    · simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨s, hs, rfl, hab⟩
  have hA : (st.filter (absent r)).map (·.id) = (st.map (·.id)).filter q := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro s hs
    exact (hq s hs).symm
  have hsub : (tail.map (·.id)).Sublist ((st.map (·.id)).filter q) := by
    have h1 := hOrd c st r tail h
    have h2 := h1.filter q
    have h3 : (tail.map (·.id)).filter q = tail.map (·.id) := by
      apply List.filter_eq_self.mpr
      intro i hi
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
      obtain ⟨a, ha, rfl⟩ := helem e he
      obtain ⟨hs, hab⟩ := List.mem_filter.mp ha
      simp only [hid]
      rw [hq a hs]; exact hab
    rw [h3] at h2; exact h2
  have hlen : (tail.map (·.id)).length = ((st.map (·.id)).filter q).length := by
    rw [← hA, List.length_map, List.length_map, hOne c st r tail h]
  have hids : tail.map (·.id) = (st.filter (absent r)).map (·.id) := by
    rw [hA]; exact hsub.eq_of_length hlen
  apply List.ext_getElem
  · have := congrArg List.length hids
    simpa using this
  · intro k h1 h2
    have e1 := helem tail[k] (List.getElem_mem h1)
    obtain ⟨a, ha, he⟩ := e1
    have hidk := congrArg (fun l => l[k]?) hids
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1] at hidk
    have hk' : k < (st.filter (absent r)).length := by simpa using h2
    rw [List.getElem?_eq_getElem hk'] at hidk
    simp only [Option.map_some, Option.some.injEq] at hidk
    have ha'm : (st.filter (absent r))[k] ∈ st.filter (absent r) := List.getElem_mem hk'
    have : a = (st.filter (absent r))[k] := by
      apply hd a (List.mem_filter.mp ha).1 _ (List.mem_filter.mp ha'm).1
      rw [he, hid] at hidk
      exact hidk
    rw [he, this]
    simp

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨tf, htf⟩ := hf.2.1 c st r
  obtain ⟨tg, htg⟩ := hg.2.1 c st r
  rw [htf, htg, tail_eq f hf c st r tf hd htf, tail_eq g hg c st r tg hd htg]

end SyncComplete
