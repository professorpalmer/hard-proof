import Sync
import SyncLaws

open Sync

namespace SyncGap

def designA : SyncImpl := ref

def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨2, 2, 2, true⟩]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  have added_b : ∀ (c : Config) (st r : List Entry),
      added designB c st r = ((st.filter (absent r)).map (adjust c)).reverse := by
    intro c st r; simp [added, designB]
  have adjust_id : ∀ c s, (adjust c s).id = s.id := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_adapter : ∀ c s, (adjust c s).adapter = s.adapter := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_model : ∀ c s, (adjust c s).model = s.model := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_enabled : ∀ c s,
      (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
    intro c s; unfold adjust
    cases h1 : s.enabled <;> cases c.enable <;> cases c.locked s.adapter <;> simp [h1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    simp [designB]
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r _ s hs ha
    rw [added_b]
    refine ⟨adjust c s, ?_, adjust_id c s, adjust_adapter c s, adjust_model c s⟩
    rw [List.mem_reverse]
    exact List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, rfl⟩
  · intro c st r _ e he
    rw [added_b, List.mem_reverse] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    obtain ⟨hs, ha⟩ := List.mem_filter.1 hs
    exact ⟨s, hs, ha, adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r _
    rw [added_b, List.length_reverse, List.length_map]
  · intro c st r _ e he
    rw [added_b, List.mem_reverse] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    obtain ⟨_, ha⟩ := List.mem_filter.1 hs
    rw [adjust_adapter, adjust_model]
    simp [absent] at ha
    simpa using ha.2
  · intro c st r _ hc e he
    rw [added_b, List.mem_reverse] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 he
    simp [adjust_enabled, hc]
  · intro c st r hd hc s hs ha hl e he hid
    rw [added_b, List.mem_reverse] at he
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 he
    obtain ⟨hs', _⟩ := List.mem_filter.1 hs'
    rw [adjust_id] at hid
    have : s' = s := same_id hd hs' hs hid
    subst this
    simp [adjust_enabled, hc, hl]
  · intro c st r _ e he hl
    rw [added_b, List.mem_reverse] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 he
    rw [adjust_adapter] at hl
    simp [adjust_enabled, hl]

theorem starter_distinct : DistinctIds starter := by
  simp [DistinctIds, starter]

theorem differ : designA config starter registry ≠ designB config starter registry := by
  simp [designA, designB, ref, config, starter, registry, adjust, absent, hasId, hasIdentity]

end SyncGap
