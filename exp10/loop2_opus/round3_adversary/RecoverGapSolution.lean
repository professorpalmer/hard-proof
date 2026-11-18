import Recover
import RecoverLaws
open Recover
namespace RecoverGap
def designA : Decide := fun _ => false
def designB : Decide := fun _ => false
def input : Case := ⟨false, false, false, none, 0⟩
theorem a_passes : Passes designA := sorry
theorem b_passes : Passes designB := sorry
theorem differ : designA input ≠ designB input := sorry
end RecoverGap
