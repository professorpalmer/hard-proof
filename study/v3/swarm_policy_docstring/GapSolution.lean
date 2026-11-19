import Types
import Laws

open HP

namespace HPGap

/-- The order of the shipped function. -/
def designA : Impl := fun x =>
  if x.refusal then Output.solo
  else if x.launch then Output.explicit
  else if x.narrow then Output.solo
  else if x.broad then Output.broad
  else Output.solo

/-- A design that obeys a refusal and ignores a launch request. -/
def designB : Impl := fun x =>
  if x.refusal then Output.solo else Output.solo

def input : Input := ⟨false, true, false, false⟩

theorem a_passes : Passes designA := by
  intro x h; simp [designA, h]

theorem b_passes : Passes designB := by
  intro x h; simp [designB]

theorem input_legal : Legal input := rfl

theorem differ : designA input ≠ designB input := by decide

end HPGap
