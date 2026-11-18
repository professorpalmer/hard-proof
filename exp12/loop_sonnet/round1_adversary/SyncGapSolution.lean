import Sync
import SyncLaws

open Sync

namespace SyncGap

def designA : SyncImpl := ref

def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c)).reverse

def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [⟨1, 1, 1, false⟩, ⟨2, 1, 1, false⟩]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  obtain ⟨k, o, a, n, d, e, l⟩ := ref_passes
  have mem : ∀ c st r x, x ∈ designB c st r ↔ x ∈ ref c st r := by
    intro c st r x
    simp [designB, ref, List.mem_append, List.mem_reverse]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r hd x hx hxr
    exact o c st r hd x ((mem c st r x).1 hx) hxr
  · intro c st r hd s hs ha
    obtain ⟨x, hx, h⟩ := a c st r hd s hs ha
    exact ⟨x, (mem c st r x).2 hx, h⟩
  · intro c st r hd x hx hxr
    exact n c st r hd x ((mem c st r x).1 hx) hxr
  · intro c st r hd he s hs ha x hx hid
    exact d c st r hd he s hs ha x ((mem c st r x).1 hx) hid
  · intro c st r hd he s hs ha hl x hx hid
    exact e c st r hd he s hs ha hl x ((mem c st r x).1 hx) hid
  · intro c st r hd s hs ha hl x hx hid
    exact l c st r hd s hs ha hl x ((mem c st r x).1 hx) hid

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' h
  simp [starter] at hs hs'
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp_all

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
