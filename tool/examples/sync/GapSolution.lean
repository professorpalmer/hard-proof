import Types
import Ref
import Laws
import RefPassesSolution

open HP

namespace HPGap

/-- The shipped code. -/
def designA : Impl := ref

/-- The same rows as the shipped code, but the new rows in the reverse order. -/
def designB : Impl := fun x => x.registry ++ ((ref x).drop x.registry.length).reverse

def input : Input := ⟨false, [], [⟨1, 1, 1, false⟩, ⟨2, 2, 2, false⟩], []⟩

theorem a_passes : Passes designA := HPRef.ref_passes

theorem addedB (x : Input) : added designB x = (added ref x).reverse := by
  simp [added, designB]

theorem memB (x : Input) (e : Entry) : e ∈ added designB x ↔ e ∈ added ref x := by
  rw [addedB]; simp

theorem b_passes : Passes designB := by
  obtain ⟨_, h2, h3, h4, h5, h6, h7⟩ := HPRef.ref_passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨_, rfl⟩
  · intro x e h
    exact h2 x e ((memB x e).1 h)
  · intro x hd s hs ha
    obtain ⟨e, he, hh⟩ := h3 x hd s hs ha
    exact ⟨e, (memB x e).2 he, hh⟩
  · intro x e h
    exact h4 x e ((memB x e).1 h)
  · intro x hc e h
    exact h5 x hc e ((memB x e).1 h)
  · intro x e h hl
    exact h6 x e ((memB x e).1 h) hl
  · intro x hd hc e h hl
    exact h7 x hd hc e ((memB x e).1 h) hl

theorem input_legal : Legal input := rfl

theorem differ : designA input ≠ designB input := by
  simp [designA, designB, ref, input, absent, hasId, hasIdentity, adjust, isLocked]

end HPGap
