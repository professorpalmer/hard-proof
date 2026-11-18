import Types
import Ref
import Laws

open HP

namespace HPRef

theorem ref_passes : Passes ref := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hl
    have h : i.lo ≤ i.hi := by simpa [Legal, legal] using hl
    -- `Output` is `Int`, but `omega` needs the type `Int` in the goal.
    show @LE.le Int _ i.lo (ref i) ∧ @LE.le Int _ (ref i) i.hi
    by_cases a : i.x < i.lo <;> by_cases b : i.x > i.hi <;> simp [ref, a, b] <;>
      first | omega | exact ⟨by omega, by omega⟩
  · intro i _ h
    simp [ref, h]
  · intro i hl h
    have hh : i.lo ≤ i.hi := by simpa [Legal, legal] using hl
    have : ¬ i.x < i.lo := by omega
    simp [ref, this, h]
  · intro i _ h1 h2
    have a : ¬ i.x < i.lo := by omega
    have b : ¬ i.x > i.hi := by omega
    simp [ref, a, b]

end HPRef
