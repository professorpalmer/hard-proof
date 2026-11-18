/-
Hard Proof, experiment 11. HUMAN-OWNED FILE.

The completeness challenge for the generated law set (`TblLaws.lean`).
The `sorry` is a hole. A prover fills it in `TblCompleteSolution.lean`.
-/
import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := sorry

end TblComplete
