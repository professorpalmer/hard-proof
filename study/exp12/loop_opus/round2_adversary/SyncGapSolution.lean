import Sync
import SyncLaws

open Sync

namespace SyncGap

def dd : List Entry → List Entry
  | [] => []
  | x :: xs => if xs.contains x then dd xs else x :: dd xs

theorem dd_sub : ∀ l : List Entry, List.Sublist (dd l) l
  | [] => List.Sublist.slnil
  | x :: xs => by
    unfold dd
    split
    · exact (dd_sub xs).cons _
    · exact (dd_sub xs).cons_cons _

theorem dd_mem : ∀ (l : List Entry) (a : Entry), a ∈ dd l ↔ a ∈ l
  | [], a => by simp [dd]
  | x :: xs, a => by
    unfold dd
    split
    · rename_i h
      have hx : x ∈ xs := by simpa using h
      rw [dd_mem xs a]
      constructor
      · intro h; exact List.mem_cons_of_mem _ h
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact hx
        · exact h
    · simp [dd_mem xs a]

def designA : SyncImpl := ref

def designB : SyncImpl :=
  fun c st r => r ++ (dd (st.filter (absent r))).map (adjust c)

def e0 : Entry := ⟨0, 0, 0, true⟩
def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [e0, e0]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  have adjust_id : ∀ (c : Config) (s : Entry), (adjust c s).id = s.id := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_adapter : ∀ (c : Config) (s : Entry), (adjust c s).adapter = s.adapter := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_model : ∀ (c : Config) (s : Entry), (adjust c s).model = s.model := by
    intro c s; unfold adjust; split <;> rfl
  have tl : ∀ {c st r t}, designB c st r = r ++ t →
      t = (dd (st.filter (absent r))).map (adjust c) := by
    intro c st r t h
    unfold designB at h
    exact (List.append_cancel_left h).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r _ e he
    unfold designB
    exact List.mem_append_left _ he
  · intro c st r t _ h e he
    rw [tl h] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, ha⟩ := List.mem_filter.mp ((dd_mem _ _).mp hs)
    exact ⟨s, hs, ha, adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r t _ h s hs ha
    rw [tl h]
    exact ⟨adjust c s, List.mem_map.mpr ⟨s, (dd_mem _ _).mpr (List.mem_filter.mpr ⟨hs, ha⟩), rfl⟩,
      adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r t _ hc h e he
    rw [tl h] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
    unfold adjust
    cases hs : s.enabled <;> simp [hs, hc]
  · intro c st r t _ h e he hl
    rw [tl h] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
    rw [adjust_adapter] at hl
    unfold adjust
    cases hs : s.enabled <;> simp [hs, hl]
  · intro c st r t hd hc h e he s' hs' hid hl
    rw [tl h] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    have hs := (List.mem_filter.mp ((dd_mem _ _).mp hs)).1
    rw [adjust_id] at hid
    have : s' = s := hd s' hs' s hs hid
    subst this
    unfold adjust
    cases he2 : s'.enabled <;> simp [he2, hc, hl]
  · intro c st r t _ h
    rw [tl h, List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext (adjust_id c)
    rw [this]
    exact (((dd_sub _).trans List.filter_sublist)).map _

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  rw [hs, hs']

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
