import Sync
import SyncLaws

open Sync

namespace SyncGap

/-- Keep the last copy of each starter, in order. -/
def dedupFirst : List Entry → List Entry
  | [] => []
  | x :: xs => if x ∈ xs then dedupFirst xs else x :: dedupFirst xs

theorem dedup_sub : ∀ (l : List Entry), (dedupFirst l).Sublist l
  | [] => by simp [dedupFirst]
  | x :: xs => by
    unfold dedupFirst
    split
    · exact (dedup_sub xs).cons x
    · exact (dedup_sub xs).cons₂ x

theorem dedup_mem : ∀ (l : List Entry) (a : Entry), a ∈ l → a ∈ dedupFirst l
  | [], a, h => by simp at h
  | x :: xs, a, h => by
    unfold dedupFirst
    split
    · rename_i hx
      rcases List.mem_cons.mp h with rfl | h
      · exact dedup_mem xs _ hx
      · exact dedup_mem xs a h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (dedup_mem xs a h)

def designA : SyncImpl := ref

def designB : SyncImpl :=
  fun c st r => r ++ ((dedupFirst st).filter (absent r)).map (adjust c)

def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 1, 1, true⟩, ⟨1, 1, 1, true⟩]
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
      designB c st r = r ++ tail → tail = ((dedupFirst st).filter (absent r)).map (adjust c) := by
    intro c st r tail h
    have h' : r ++ ((dedupFirst st).filter (absent r)).map (adjust c) = r ++ tail := h
    exact (List.append_cancel_left h').symm
  unfold Passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r i hi
    show (r ++ ((dedupFirst st).filter (absent r)).map (adjust c))[i]? = r[i]?
    exact List.getElem?_append_left hi
  · intro c st r
    exact ⟨((dedupFirst st).filter (absent r)).map (adjust c), rfl⟩
  · intro c st r tail h e he
    rw [hcut c st r tail h] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, hab⟩ := List.mem_filter.mp ha
    exact ⟨a, (dedup_sub st).subset hs, hab, hid c a, had c a, hmd c a⟩
  · intro c st r tail h s hs hab
    refine ⟨adjust c s, ?_, hid c s, had c s, hmd c s⟩
    rw [hcut c st r tail h]
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨dedup_mem st s hs, hab⟩, rfl⟩
  · intro c st r tail h e he
    rw [hcut c st r tail h] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨_, hab⟩ := List.mem_filter.mp ha
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    simpa [had, hmd] using hab.2
  · intro c st r tail h e he
    rw [hcut c st r tail h] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, _⟩ := List.mem_filter.mp ha
    exact ⟨a, (dedup_sub st).subset hs, hid c a, had c a, hmd c a, hen c a⟩
  · intro c st r tail h
    rw [hcut c st r tail h, List.map_map]
    have h1 : (fun x => (adjust c x).id) = fun x => x.id := funext (hid c)
    have h2 : ((dedupFirst st).filter (absent r)).Sublist st :=
      List.filter_sublist.trans (dedup_sub st)
    simpa [Function.comp_def, h1] using h2.map (fun e => e.id)

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp only [starter, List.mem_cons, List.not_mem_nil, or_false] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> rfl

theorem differ : designA config starter registry ≠ designB config starter registry := by
  intro h
  have := congrArg List.length h
  simp [designA, designB, ref, config, starter, registry, absent, hasId, hasIdentity, adjust, dedupFirst] at this

end SyncGap
