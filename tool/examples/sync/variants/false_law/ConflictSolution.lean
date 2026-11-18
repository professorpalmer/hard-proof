-- hardproof-law: NewAlwaysEnabled
import Types
import Ref
import Laws

open HP

namespace HPConflict

/-- No `--enable` flag, one starter entry, an empty registry. -/
def input : Input := ⟨false, [], [⟨1, 1, 1, true⟩], []⟩

theorem input_legal : Legal input := rfl

theorem ref_breaks : ¬ NewAlwaysEnabled ref := by
  intro h
  have := h input ⟨1, 1, 1, false⟩
    (by simp [added, ref, input, absent, hasId, hasIdentity, adjust, isLocked])
  simp at this

end HPConflict
