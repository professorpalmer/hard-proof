import Tbl
import TblLaws

open Tbl

namespace TblComplete

set_option maxHeartbeats 40000000 in
/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15,
    l16, l17, l18, l19, l20, l21, l22, l23, l24, l25, l26, l27, l28, l29, l30, l31⟩ := hf
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,
    m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31⟩ := hg
  cases c with
  | mk b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;>
    first
      | exact (l0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l1 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m1 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l2 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m2 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l3 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m3 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l4 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m4 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l5 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m5 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l6 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m6 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l7 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m7 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l8 _ (by rfl) (by rfl) (by rfl)).trans (m8 _ (by rfl) (by rfl) (by rfl)).symm
      | exact (l9 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m9 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l10 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m10 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l11 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m11 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l12 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m12 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l13 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m13 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l14 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m14 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l15 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m15 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l16 _ (by rfl) (by rfl) (by rfl) (by rfl)).trans (m16 _ (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l17 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m17 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l18 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m18 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l19 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m19 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l20 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m20 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l21 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m21 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l22 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m22 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l23 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m23 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l24 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m24 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l25 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m25 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l26 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m26 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l27 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m27 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l28 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m28 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l29 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (m29 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l30 _ (by rfl) (by rfl) (by rfl) (by rfl)).trans (m30 _ (by rfl) (by rfl) (by rfl) (by rfl)).symm
      | exact (l31 _ (by rfl) (by rfl)).trans (m31 _ (by rfl) (by rfl)).symm

end TblComplete
