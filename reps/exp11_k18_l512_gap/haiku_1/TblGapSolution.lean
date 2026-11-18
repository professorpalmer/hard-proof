import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule: the reference rule. -/
def designA : Decide := ref

/-- The second recovery rule: the reference rule, with the answer flipped on the region that no law
constrains. The law numbered 349 is absent from `TblLaws.lean`. The region is the 256 cases that
match the ten literals below. -/
def designB : Decide := fun c =>
  if c.b4 = true ∧ c.b1 = false ∧ c.b14 = false ∧ c.b3 = true ∧ c.b8 = true ∧
      c.b16 = true ∧ c.b6 = false ∧ c.b10 = false ∧ c.b12 = false ∧ c.b15 = true
  then !ref c else ref c

/-- A case in the unconstrained region. -/
def input : Case :=
  { b0 := false, b1 := false, b2 := false, b3 := true, b4 := true, b5 := false,
    b6 := false, b7 := false, b8 := true, b9 := false, b10 := false, b11 := false,
    b12 := false, b13 := false, b14 := false, b15 := true, b16 := true, b17 := false }

theorem a_passes : Passes designA := by
  unfold designA Passes
    Group0 Group1 Group2 Group3 Group4 Group5 Group6 Group7 Group8 Group9 Group10
    Group11 Group12 Group13 Group14 Group15 Group16 Group17 Group18 Group19 Group20
    Group21 Group22 Group23 Group24 Group25 Group26 Group27 Group28 Group29 Group30 Group31
  repeat' constructor
  all_goals (intro c; intros; simp_all [ref])

theorem b_passes : Passes designB := by
  unfold designB Passes
    Group0 Group1 Group2 Group3 Group4 Group5 Group6 Group7 Group8 Group9 Group10
    Group11 Group12 Group13 Group14 Group15 Group16 Group17 Group18 Group19 Group20
    Group21 Group22 Group23 Group24 Group25 Group26 Group27 Group28 Group29 Group30 Group31
  repeat' constructor
  all_goals (intro c; intros; simp_all [ref])

theorem differ : designA input ≠ designB input := by
  decide

end TblGap
