import Sync
import SyncLaws

open Sync

namespace SyncGap

def designA : SyncImpl := ref

def designB : SyncImpl := fun c st r => r ++ (ref c st r |>.drop r.length).reverse

def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [⟨1, 1, 1, false⟩, ⟨2, 2, 2, false⟩]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

private theorem addedB (c : Config) (st r : List Entry) :
    added designB c st r = (added ref c st r).reverse := by
  simp [added, designB]

private theorem memB (c : Config) (st r : List Entry) (e : Entry) :
    e ∈ added designB c st r ↔ e ∈ added ref c st r := by
  rw [addedB]; simp

theorem b_passes : Passes designB := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ref_passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r
    exact ⟨_, rfl⟩
  · intro c st r e h
    exact h2 c st r e ((memB c st r e).1 h)
  · intro c st r hd s hs ha
    obtain ⟨e, he, hh⟩ := h3 c st r hd s hs ha
    exact ⟨e, (memB c st r e).2 he, hh⟩
  · intro c st r e h
    exact h4 c st r e ((memB c st r e).1 h)
  · intro c st r hc e h
    exact h5 c st r hc e ((memB c st r e).1 h)
  · intro c st r e h hl
    exact h6 c st r e ((memB c st r e).1 h) hl
  · intro c st r hd hc e h hl
    exact h7 c st r hd hc e ((memB c st r e).1 h) hl
  · intro c st r
    rw [addedB]
    simp [designB, added]

theorem starter_distinct : DistinctIds starter := by
  simp [DistinctIds, starter]

theorem differ : designA config starter registry ≠ designB config starter registry := by
  simp [designA, designB, ref, config, starter, registry, absent, hasId, hasIdentity, adjust]

end SyncGap
