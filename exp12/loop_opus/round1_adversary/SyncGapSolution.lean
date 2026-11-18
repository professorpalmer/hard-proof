import Sync
import SyncLaws

open Sync

namespace SyncGap

def designA : SyncImpl := ref

def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [⟨1, 0, 1, false⟩, ⟨2, 0, 2, false⟩]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  have adjust_id : ∀ (c : Config) (s : Entry), (adjust c s).id = s.id := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_adapter : ∀ (c : Config) (s : Entry), (adjust c s).adapter = s.adapter := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_model : ∀ (c : Config) (s : Entry), (adjust c s).model = s.model := by
    intro c s; unfold adjust; split <;> rfl
  have tail : ∀ {c st r t}, designB c st r = r ++ t →
      t = ((st.filter (absent r)).map (adjust c)).reverse := by
    intro c st r t h
    unfold designB at h
    exact (List.append_cancel_left h).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r _ e he
    unfold designB
    exact List.mem_append_left _ he
  · intro c st r t _ h e he
    rw [tail h, List.mem_reverse] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, ha⟩ := List.mem_filter.mp hs
    exact ⟨s, hs, ha, adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r t _ h s hs ha
    rw [tail h]
    exact ⟨adjust c s, List.mem_reverse.mpr (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩),
      adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r t _ hc h e he
    rw [tail h, List.mem_reverse] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
    unfold adjust
    cases hs : s.enabled <;> simp [hs, hc]
  · intro c st r t _ h e he hl
    rw [tail h, List.mem_reverse] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
    rw [adjust_adapter] at hl
    unfold adjust
    cases hs : s.enabled <;> simp [hs, hl]
  · intro c st r t hd hc h e he s' hs' hid hl
    rw [tail h, List.mem_reverse] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    have hs := (List.mem_filter.mp hs).1
    rw [adjust_id] at hid
    have : s' = s := hd s' hs' s hs hid
    subst this
    unfold adjust
    cases he2 : s'.enabled <;> simp [he2, hc, hl]

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp [starter] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> first | rfl | (simp at h)

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
