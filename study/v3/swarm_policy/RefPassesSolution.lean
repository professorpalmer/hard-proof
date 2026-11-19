import Types
import Ref
import Laws

open HP

namespace HPRef

theorem ref_passes : Passes ref := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x h; simp [ref, h]
  · intro x h1 h2; simp [ref, h1, h2]
  · intro x h1 h2 h3; simp [ref, h1, h2, h3]
  · intro x h1 h2 h3 h4; simp [ref, h1, h2, h3, h4]
  · intro x h1 h2 h3 h4; simp [ref, h1, h2, h3, h4]

end HPRef
