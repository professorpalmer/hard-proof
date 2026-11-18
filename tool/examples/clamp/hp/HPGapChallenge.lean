-- hardproof: TOOL-OWNED FILE. The tool writes it again before each check.
import Types
import Laws

open HP

namespace HPGap

/-- The first design. -/
def designA : Impl := sorry

/-- The second design. -/
def designB : Impl := sorry

/-- The input on which the two designs differ. -/
def input : Input := sorry

/-- The first design passes each law. -/
theorem a_passes : Passes designA := sorry

/-- The second design passes each law. -/
theorem b_passes : Passes designB := sorry

/-- The input is legal. -/
theorem input_legal : Legal input := sorry

/-- The two designs give different outputs on the input. -/
theorem differ : designA input ≠ designB input := sorry

end HPGap
