import Lean
import Tbl
import TblLaws

open Tbl
open Lean Meta Elab Tactic

namespace TblComplete

theorem ite_split {p : Prop} [Decidable p] {a b x : Bool}
    (h1 : p → x = a) (h2 : ¬p → x = b) : x = if p then a else b := by
  by_cases hp : p
  · rw [ite_eq_left hp]; exact h1 hp
  · rw [ite_eq_right hp]; exact h2 hp

theorem not_true_eq {b : Bool} (h : ¬b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- Close a goal `f c = v` with the one leaf law whose conditions are all hypotheses. -/
elab "leaf_close" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let fn := ty.getAppFn
      unless fn.isConst && (fn.constName!.toString.startsWith "Tbl.Leaf") do continue
      let s ← saveState
      try
        let gs ← goal.apply ldecl.toExpr
        for g in gs do
          unless (← g.isAssigned) do g.assumption
        return
      catch _ => s.restore
    throwError "leaf_close: no leaf fits"

set_option maxHeartbeats 0 in
theorem agree_ref (f : Decide) (hf : Passes f) (c : Case) : f c = ref c := by
  simp only [Passes, Group0, Group1, Group2, Group3, Group4, Group5, Group6, Group7,
    Group8, Group9, Group10, Group11, Group12, Group13, Group14, Group15, Group16,
    Group17, Group18, Group19, Group20, Group21, Group22, Group23, Group24, Group25,
    Group26, Group27, Group28, Group29, Group30, Group31, and_assoc] at hf
  repeat obtain ⟨_, hf⟩ := hf
  unfold ref
  repeat' (apply ite_split <;> intro h <;> try replace h := not_true_eq h)
  all_goals leaf_close

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  rw [agree_ref f hf c, agree_ref g hg c]

end TblComplete
