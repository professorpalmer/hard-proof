import Tbl
import TblLaws

open Tbl

namespace TblComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31⟩ := hf
  obtain ⟨G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27, G28, G29, G30, G31⟩ := hg
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := c
  cases b0 with
  | false =>
    cases b2 with
    | false =>
      cases b4 with
      | false =>
        exact (F11 _ rfl rfl rfl).trans (G11 _ rfl rfl rfl).symm
      | true =>
        exact (F30 _ rfl rfl rfl).trans (G30 _ rfl rfl rfl).symm
    | true =>
      exact (F2 _ rfl rfl).trans (G2 _ rfl rfl).symm
  | true =>
    cases b4 with
    | false =>
      cases b1 with
      | false =>
        cases b8 with
        | false =>
          cases b6 with
          | false =>
            cases b9 with
            | false =>
              cases b7 with
              | false =>
                exact (F10 _ rfl rfl rfl rfl rfl rfl rfl).trans (G10 _ rfl rfl rfl rfl rfl rfl rfl).symm
              | true =>
                exact (F19 _ rfl rfl rfl rfl rfl rfl rfl).trans (G19 _ rfl rfl rfl rfl rfl rfl rfl).symm
            | true =>
              cases b2 with
              | false =>
                exact (F21 _ rfl rfl rfl rfl rfl rfl rfl).trans (G21 _ rfl rfl rfl rfl rfl rfl rfl).symm
              | true =>
                exact (F17 _ rfl rfl rfl rfl rfl rfl rfl).trans (G17 _ rfl rfl rfl rfl rfl rfl rfl).symm
          | true =>
            cases b7 with
            | false =>
              exact (F8 _ rfl rfl rfl rfl rfl rfl).trans (G8 _ rfl rfl rfl rfl rfl rfl).symm
            | true =>
              exact (F23 _ rfl rfl rfl rfl rfl rfl).trans (G23 _ rfl rfl rfl rfl rfl rfl).symm
        | true =>
          cases b3 with
          | false =>
            cases b6 with
            | false =>
              cases b5 with
              | false =>
                exact (F6 _ rfl rfl rfl rfl rfl rfl rfl).trans (G6 _ rfl rfl rfl rfl rfl rfl rfl).symm
              | true =>
                cases b7 with
                | false =>
                  cases b9 with
                  | false =>
                    cases b2 with
                    | false =>
                      exact (F1 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (G1 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    | true =>
                      exact (F5 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (G5 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  | true =>
                    exact (F28 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (G28 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                | true =>
                  exact (F0 _ rfl rfl rfl rfl rfl rfl rfl rfl).trans (G0 _ rfl rfl rfl rfl rfl rfl rfl rfl).symm
            | true =>
              cases b5 with
              | false =>
                cases b2 with
                | false =>
                  exact (F15 _ rfl rfl rfl rfl rfl rfl rfl rfl).trans (G15 _ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                | true =>
                  cases b9 with
                  | false =>
                    exact (F9 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (G9 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  | true =>
                    exact (F18 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (G18 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
              | true =>
                exact (F12 _ rfl rfl rfl rfl rfl rfl rfl).trans (G12 _ rfl rfl rfl rfl rfl rfl rfl).symm
          | true =>
            cases b7 with
            | false =>
              cases b5 with
              | false =>
                cases b6 with
                | false =>
                  exact (F20 _ rfl rfl rfl rfl rfl rfl rfl rfl).trans (G20 _ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                | true =>
                  exact (F16 _ rfl rfl rfl rfl rfl rfl rfl rfl).trans (G16 _ rfl rfl rfl rfl rfl rfl rfl rfl).symm
              | true =>
                exact (F4 _ rfl rfl rfl rfl rfl rfl rfl).trans (G4 _ rfl rfl rfl rfl rfl rfl rfl).symm
            | true =>
              exact (F14 _ rfl rfl rfl rfl rfl rfl).trans (G14 _ rfl rfl rfl rfl rfl rfl).symm
      | true =>
        exact (F22 _ rfl rfl rfl).trans (G22 _ rfl rfl rfl).symm
    | true =>
      cases b9 with
      | false =>
        cases b6 with
        | false =>
          cases b8 with
          | false =>
            cases b5 with
            | false =>
              cases b2 with
              | false =>
                cases b7 with
                | false =>
                  exact (F13 _ rfl rfl rfl rfl rfl rfl rfl rfl).trans (G13 _ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                | true =>
                  exact (F29 _ rfl rfl rfl rfl rfl rfl rfl rfl).trans (G29 _ rfl rfl rfl rfl rfl rfl rfl rfl).symm
              | true =>
                exact (F25 _ rfl rfl rfl rfl rfl rfl rfl).trans (G25 _ rfl rfl rfl rfl rfl rfl rfl).symm
            | true =>
              exact (F26 _ rfl rfl rfl rfl rfl rfl).trans (G26 _ rfl rfl rfl rfl rfl rfl).symm
          | true =>
            exact (F24 _ rfl rfl rfl rfl rfl).trans (G24 _ rfl rfl rfl rfl rfl).symm
        | true =>
          exact (F31 _ rfl rfl rfl rfl).trans (G31 _ rfl rfl rfl rfl).symm
      | true =>
        cases b8 with
        | false =>
          cases b3 with
          | false =>
            exact (F27 _ rfl rfl rfl rfl rfl).trans (G27 _ rfl rfl rfl rfl rfl).symm
          | true =>
            exact (F3 _ rfl rfl rfl rfl rfl).trans (G3 _ rfl rfl rfl rfl rfl).symm
        | true =>
          exact (F7 _ rfl rfl rfl rfl).trans (G7 _ rfl rfl rfl rfl).symm

end TblComplete
