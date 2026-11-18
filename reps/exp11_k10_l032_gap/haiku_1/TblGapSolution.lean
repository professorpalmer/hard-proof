import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- Two cases on bools: a statement over all `Case` values holds when it holds for every tuple of bools. -/
theorem forall_case (P : Case → Prop)
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      P { b0 := b0, b1 := b1, b2 := b2, b3 := b3, b4 := b4,
          b5 := b5, b6 := b6, b7 := b7, b8 := b8, b9 := b9 }) :
    ∀ c : Case, P c := by
  intro c
  cases c
  exact h _ _ _ _ _ _ _ _ _ _

/-- The first recovery rule. -/
def designA : Decide := ref

/-- The cases that no law constrains: the leaves skip them. -/
def gapCase (c : Case) : Bool :=
  c.b2 && !c.b6 && !c.b8 && c.b9 && c.b4 && !c.b7 && !c.b0

/-- The second recovery rule. -/
def designB : Decide := fun c => if gapCase c then !ref c else ref c

/-- The case on which the two rules differ. -/
def input : Case :=
  { b0 := false, b1 := false, b2 := true, b3 := false, b4 := true,
    b5 := false, b6 := false, b7 := false, b8 := false, b9 := true }

theorem ref_passes_all : Passes ref := by
  unfold Passes
  repeat' apply And.intro
  all_goals (apply forall_case; decide +kernel)

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := ref_passes_all

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes
  repeat' apply And.intro
  all_goals (apply forall_case; decide +kernel)

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide +kernel

end TblGap
