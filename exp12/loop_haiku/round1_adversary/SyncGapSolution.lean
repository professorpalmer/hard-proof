import Sync
import SyncLaws

open Sync

namespace SyncGap

def designA : SyncImpl := ref

def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 0, 1, true⟩, ⟨2, 0, 2, true⟩]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
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
  have hcut : ∀ (c : Config) (st r tail : List Entry),
      designB c st r = r ++ tail → tail = ((st.filter (absent r)).map (adjust c)).reverse := by
    intro c st r tail h
    have h' : r ++ ((st.filter (absent r)).map (adjust c)).reverse = r ++ tail := h
    exact (List.append_cancel_left h').symm
  unfold Passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r i hi
    show (r ++ ((st.filter (absent r)).map (adjust c)).reverse)[i]? = r[i]?
    exact List.getElem?_append_left hi
  · intro c st r
    exact ⟨((st.filter (absent r)).map (adjust c)).reverse, rfl⟩
  · intro c st r tail h e he
    rw [hcut c st r tail h, List.mem_reverse] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, hab⟩ := List.mem_filter.mp ha
    exact ⟨a, hs, hab, hid c a, had c a, hmd c a⟩
  · intro c st r tail h s hs hab
    refine ⟨adjust c s, ?_, hid c s, had c s, hmd c s⟩
    rw [hcut c st r tail h, List.mem_reverse]
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hab⟩, rfl⟩
  · intro c st r tail h e he
    rw [hcut c st r tail h, List.mem_reverse] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨_, hab⟩ := List.mem_filter.mp ha
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    simpa [had, hmd] using hab.2
  · intro c st r tail h e he
    rw [hcut c st r tail h, List.mem_reverse] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, _⟩ := List.mem_filter.mp ha
    exact ⟨a, hs, hid c a, had c a, hmd c a, hen c a⟩

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp [starter] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp_all

theorem differ : designA config starter registry ≠ designB config starter registry := by
  simp [designA, designB, ref, config, starter, registry, absent, hasId, hasIdentity, adjust]

end SyncGap
