import Types
import Ref
import Laws

open HP

namespace HPRef

theorem added_ref (x : Input) : added ref x = (x.starter.filter (absent x.registry)).map (adjust x) := by
  simp [added, ref]

theorem mem_added_ref (x : Input) (e : Entry) (h : e ∈ added ref x) :
    ∃ s ∈ x.starter, absent x.registry s = true ∧ adjust x s = e := by
  rw [added_ref] at h
  simp only [List.mem_map, List.mem_filter] at h
  obtain ⟨s, ⟨hs, ha⟩, he⟩ := h
  exact ⟨s, hs, ha, he⟩

theorem adjust_fields (x : Input) (s : Entry) :
    (adjust x s).id = s.id ∧ (adjust x s).adapter = s.adapter ∧ (adjust x s).model = s.model := by
  unfold adjust
  split <;> simp

theorem ref_passes : Passes ref := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨_, rfl⟩
  · intro x e h
    obtain ⟨s, hs, ha, he⟩ := mem_added_ref x e h
    obtain ⟨h1, h2, h3⟩ := adjust_fields x s
    subst he
    exact ⟨s, hs, ha, h1, h2, h3⟩
  · intro x _ s hs ha
    refine ⟨adjust x s, ?_, adjust_fields x s⟩
    rw [added_ref]
    exact List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, rfl⟩
  · intro x e h
    obtain ⟨s, hs, ha, he⟩ := mem_added_ref x e h
    obtain ⟨_, h2, h3⟩ := adjust_fields x s
    subst he
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
    rw [h2, h3]
    simpa using ha.2
  · intro x hc e h
    obtain ⟨s, hs, ha, he⟩ := mem_added_ref x e h
    subst he
    unfold adjust
    split <;> simp_all
  · intro x e h hl
    obtain ⟨s, hs, ha, he⟩ := mem_added_ref x e h
    subst he
    have hl' : isLocked x s.adapter = true := by rw [(adjust_fields x s).2.1] at hl; exact hl
    unfold adjust
    split <;> simp_all
  · intro x _ hc e h hl
    obtain ⟨s, hs, ha, he⟩ := mem_added_ref x e h
    subst he
    refine ⟨s, hs, ha, (adjust_fields x s).1, ?_⟩
    have hl' : isLocked x s.adapter = false := by rw [(adjust_fields x s).2.1] at hl; exact hl
    simp [adjust, hc, hl']

end HPRef
