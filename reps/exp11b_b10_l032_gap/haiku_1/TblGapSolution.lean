/-
Hard Proof, experiment 11. Adversary solution: the laws do not determine the rule.

Two rules pass every law and differ on one case. The case `input` is covered
by no law. `designA` gives `false` there (no law fires). `designB` flips the
answer on exactly that case.
-/
import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The answer table: the OR of each premise of a law that says `true`. -/
def table (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Bool :=
    (b4 && b9 && b0 && !b8 && b3)
    || (b6 && b0 && !b9 && b4)
    || (!b1 && !b7 && !b8 && !b4 && b0 && b6)
    || (!b1 && b0 && !b6 && b9 && !b8 && !b4 && !b2)
    || (b8 && !b1 && b5 && !b3 && b0 && b9 && !b4 && !b6 && !b7)
    || (!b5 && !b3 && b8 && !b4 && !b6 && b0 && !b1)
    || (b8 && b4 && !b6 && !b9 && b0)
    || (b9 && b8 && b4 && b0)
    || (b0 && b8 && b3 && b7 && !b1 && !b4)
    || (!b0 && b2)

/-- The case on which the two rules differ. It matches no law. -/
def input : Case := ⟨true, false, false, false, false, false, false, true, false, false⟩

/-- The first recovery rule: the law table. -/
def designA : Decide := fun c => table c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9

/-- The second recovery rule: the law table, flipped on `input` only. -/
def designB : Decide := fun c =>
  table c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9 != (c.b0 && !c.b1 && !c.b2 && !c.b3 && !c.b4 && !c.b5 && !c.b6 && c.b7 && !c.b8 && !c.b9)

theorem keyA_0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = true → b3 = false → b4 = false → b6 = false → b0 = true → b1 = false → b8 = true → b7 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_1 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b9 = true → b0 = true → b8 = false → b3 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b9 = true → b0 = true → b8 = false → b4 = true → b3 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_3 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = true → b7 = false → b9 = false → b8 = false → b1 = false → b6 = false → b4 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_4 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = false → b7 = false → b3 = true → b4 = false → b1 = false → b8 = true → b6 = false → b0 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_5 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b8 = true → b4 = false → b0 = true → b5 = false → b1 = false → b2 = false → b3 = false → b6 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_6 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b6 = false → b9 = false → b4 = false → b8 = true → b7 = false → b5 = true → b1 = false → b3 = false → b2 = true → b0 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_7 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b4 = false → b7 = true → b8 = false → b6 = true → b0 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_8 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b6 = false → b1 = false → b0 = true → b3 = false → b9 = false → b4 = false → b7 = false → b2 = false → b5 = true → b8 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_9 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b6 = true → b0 = true → b9 = false → b4 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_10 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = false → b2 = false → b7 = true → b9 = false → b0 = true → b4 = true → b8 = false → b6 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_11 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = true → b6 = true → b4 = false → b1 = false → b3 = false → b0 = true → b8 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_12 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b7 = false → b8 = false → b4 = false → b0 = true → b6 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_13 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b9 = false → b1 = false → b0 = true → b2 = true → b3 = false → b8 = true → b4 = false → b6 = true → b5 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_14 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b9 = false → b6 = false → b2 = true → b8 = false → b0 = true → b5 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_15 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b0 = true → b6 = false → b9 = true → b8 = false → b4 = false → b2 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_16 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b8 = true → b1 = false → b5 = true → b3 = false → b0 = true → b9 = true → b4 = false → b6 = false → b7 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_17 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = false → b3 = false → b8 = true → b4 = false → b6 = false → b0 = true → b1 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_18 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = false → b1 = true → b0 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_19 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = false → b6 = false → b1 = false → b9 = true → b2 = true → b8 = false → b0 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_20 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = true → b5 = false → b6 = false → b2 = false → b8 = false → b7 = false → b9 = false → b4 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_21 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b8 = true → b4 = true → b6 = false → b9 = false → b0 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_22 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b9 = true → b8 = true → b4 = true → b0 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_23 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = true → b4 = false → b0 = true → b1 = false → b3 = true → b7 = false → b8 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_24 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = true → b8 = true → b3 = true → b7 = true → b1 = false → b4 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_25 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = false → b2 = true → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyA_26 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b2 = false → b0 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_27 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b9 = false → b0 = true → b6 = false → b5 = true → b8 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_28 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b0 = true → b8 = true → b4 = false → b9 = true → b6 = true → b2 = true → b3 = false → b5 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_29 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b2 = false → b4 = false → b0 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyA_30 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b7 = false → b6 = true → b0 = true → b1 = false → b3 = true → b8 = true → b4 = false → b5 = false → (table) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel


theorem keyB_0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = true → b3 = false → b4 = false → b6 = false → b0 = true → b1 = false → b8 = true → b7 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_1 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b9 = true → b0 = true → b8 = false → b3 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b9 = true → b0 = true → b8 = false → b4 = true → b3 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_3 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = true → b7 = false → b9 = false → b8 = false → b1 = false → b6 = false → b4 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_4 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = false → b7 = false → b3 = true → b4 = false → b1 = false → b8 = true → b6 = false → b0 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_5 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b8 = true → b4 = false → b0 = true → b5 = false → b1 = false → b2 = false → b3 = false → b6 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_6 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b6 = false → b9 = false → b4 = false → b8 = true → b7 = false → b5 = true → b1 = false → b3 = false → b2 = true → b0 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_7 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b4 = false → b7 = true → b8 = false → b6 = true → b0 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_8 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b6 = false → b1 = false → b0 = true → b3 = false → b9 = false → b4 = false → b7 = false → b2 = false → b5 = true → b8 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_9 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b6 = true → b0 = true → b9 = false → b4 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_10 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = false → b2 = false → b7 = true → b9 = false → b0 = true → b4 = true → b8 = false → b6 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_11 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = true → b6 = true → b4 = false → b1 = false → b3 = false → b0 = true → b8 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_12 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b7 = false → b8 = false → b4 = false → b0 = true → b6 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_13 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b9 = false → b1 = false → b0 = true → b2 = true → b3 = false → b8 = true → b4 = false → b6 = true → b5 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_14 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b9 = false → b6 = false → b2 = true → b8 = false → b0 = true → b5 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_15 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b0 = true → b6 = false → b9 = true → b8 = false → b4 = false → b2 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_16 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b8 = true → b1 = false → b5 = true → b3 = false → b0 = true → b9 = true → b4 = false → b6 = false → b7 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_17 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = false → b3 = false → b8 = true → b4 = false → b6 = false → b0 = true → b1 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_18 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = false → b1 = true → b0 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_19 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = false → b6 = false → b1 = false → b9 = true → b2 = true → b8 = false → b0 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_20 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = true → b5 = false → b6 = false → b2 = false → b8 = false → b7 = false → b9 = false → b4 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_21 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b8 = true → b4 = true → b6 = false → b9 = false → b0 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_22 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b9 = true → b8 = true → b4 = true → b0 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_23 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b5 = true → b4 = false → b0 = true → b1 = false → b3 = true → b7 = false → b8 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_24 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = true → b8 = true → b3 = true → b7 = true → b1 = false → b4 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_25 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b0 = false → b2 = true → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true) := by
  decide +kernel

theorem keyB_26 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b2 = false → b0 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_27 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b4 = true → b9 = false → b0 = true → b6 = false → b5 = true → b8 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_28 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b1 = false → b0 = true → b8 = true → b4 = false → b9 = true → b6 = true → b2 = true → b3 = false → b5 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_29 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b2 = false → b4 = false → b0 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel

theorem keyB_30 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (b7 = false → b6 = true → b0 = true → b1 = false → b3 = true → b8 = true → b4 = false → b5 = false → (fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 => table b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 != (b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && b7 && !b8 && !b9)) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = false) := by
  decide +kernel


/-- The first rule passes each law. -/
theorem a_passes : Passes designA := ⟨fun c => keyA_0 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_1 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_2 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_3 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_4 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_5 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_6 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_7 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_8 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_9 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_10 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_11 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_12 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_13 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_14 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_15 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_16 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_17 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_18 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_19 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_20 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_21 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_22 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_23 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_24 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_25 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_26 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_27 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_28 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_29 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyA_30 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9⟩

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := ⟨fun c => keyB_0 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_1 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_2 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_3 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_4 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_5 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_6 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_7 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_8 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_9 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_10 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_11 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_12 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_13 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_14 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_15 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_16 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_17 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_18 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_19 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_20 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_21 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_22 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_23 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_24 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_25 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_26 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_27 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_28 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_29 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9,
    fun c => keyB_30 c.b0 c.b1 c.b2 c.b3 c.b4 c.b5 c.b6 c.b7 c.b8 c.b9⟩

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide +kernel

end TblGap
