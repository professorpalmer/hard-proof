import Sync
import SyncLaws

open Sync

namespace SyncGap

def dd : List Entry → List Entry
  | [] => []
  | x :: xs => x :: (dd xs).filter (fun y => decide (y ≠ x))

theorem dd_sublist : ∀ l : List Entry, (dd l).Sublist l
  | [] => List.Sublist.slnil
  | x :: xs => by
    unfold dd
    exact (((dd_sublist xs).trans (List.Sublist.refl _)).filter _ |>.trans (List.filter_sublist)).cons₂ x
      |> fun h => h

theorem dd_mem : ∀ (l : List Entry) (y : Entry), y ∈ l → y ∈ dd l
  | [], y, h => by simp at h
  | x :: xs, y, h => by
    unfold dd
    by_cases hy : y = x
    · subst hy; exact List.mem_cons_self
    · have : y ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hy
        · exact h
      exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨dd_mem xs y this, by simpa using hy⟩)

def designA : SyncImpl := ref

def designB : SyncImpl := fun c st r => ref c (dd st) r

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
      designB c st r = r ++ tail → tail = ((dd st).filter (absent r)).map (adjust c) := by
    intro c st r tail h
    have h' : r ++ ((dd st).filter (absent r)).map (adjust c) = r ++ tail := h
    exact (List.append_cancel_left h').symm
  unfold Passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r i hi
    show (r ++ ((dd st).filter (absent r)).map (adjust c))[i]? = r[i]?
    exact List.getElem?_append_left hi
  · intro c st r
    exact ⟨((dd st).filter (absent r)).map (adjust c), rfl⟩
  · intro c st r tail h e he
    rw [hcut c st r tail h] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, hab⟩ := List.mem_filter.mp ha
    exact ⟨a, (dd_sublist st).subset hs, hab, hid c a, had c a, hmd c a⟩
  · intro c st r tail h s hs hab
    refine ⟨adjust c s, ?_, hid c s, had c s, hmd c s⟩
    rw [hcut c st r tail h]
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨dd_mem st s hs, hab⟩, rfl⟩
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
    exact ⟨a, (dd_sublist st).subset hs, hid c a, had c a, hmd c a, hen c a⟩
  · intro c st r tail _ h
    rw [hcut c st r tail h, List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext (hid c)
    rw [this]
    exact (List.filter_sublist.map _).trans (((dd_sublist st)).map _)

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  rw [hs, hs']

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
