import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  unfold Passes at hf hg
  obtain ⟨F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31, F32, F33, F34, F35, F36, F37, F38, F39, F40, F41, F42, F43, F44, F45, F46, F47, F48, F49, F50, F51, F52, F53, F54, F55, F56, F57, F58, F59, F60, F61, F62, F63, F64, F65, F66, F67, F68, F69, F70, F71, F72, F73, F74, F75, F76, F77, F78, F79, F80, F81, F82, F83, F84, F85, F86, F87, F88, F89, F90, F91, F92, F93, F94, F95, F96, F97, F98, F99, F100, F101, F102, F103, F104, F105, F106, F107, F108, F109, F110, F111, F112, F113, F114, F115, F116, F117, F118, F119, F120, F121, F122, F123, F124, F125, F126, F127⟩ := hf
  obtain ⟨G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27, G28, G29, G30, G31, G32, G33, G34, G35, G36, G37, G38, G39, G40, G41, G42, G43, G44, G45, G46, G47, G48, G49, G50, G51, G52, G53, G54, G55, G56, G57, G58, G59, G60, G61, G62, G63, G64, G65, G66, G67, G68, G69, G70, G71, G72, G73, G74, G75, G76, G77, G78, G79, G80, G81, G82, G83, G84, G85, G86, G87, G88, G89, G90, G91, G92, G93, G94, G95, G96, G97, G98, G99, G100, G101, G102, G103, G104, G105, G106, G107, G108, G109, G110, G111, G112, G113, G114, G115, G116, G117, G118, G119, G120, G121, G122, G123, G124, G125, G126, G127⟩ := hg
  cases hb2 : c.b2 with
  | false =>
    cases hb13 : c.b13 with
    | false =>
      cases hb5 : c.b5 with
      | false =>
        cases hb9 : c.b9 with
        | false =>
          exact (F0 c (by assumption) (by assumption) (by assumption) (by assumption)).trans (G0 c (by assumption) (by assumption) (by assumption) (by assumption)).symm
        | true =>
          exact (F1 c (by assumption) (by assumption) (by assumption) (by assumption)).trans (G1 c (by assumption) (by assumption) (by assumption) (by assumption)).symm
      | true =>
        cases hb8 : c.b8 with
        | false =>
          cases hb1 : c.b1 with
          | false =>
            exact (F2 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G2 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            exact (F3 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G3 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
        | true =>
          cases hb9 : c.b9 with
          | false =>
            cases hb0 : c.b0 with
            | false =>
              cases hb12 : c.b12 with
              | false =>
                cases hb10 : c.b10 with
                | false =>
                  exact (F4 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G4 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F5 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G5 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F6 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G6 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              exact (F7 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G7 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            exact (F8 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G8 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
    | true =>
      cases hb11 : c.b11 with
      | false =>
        cases hb0 : c.b0 with
        | false =>
          cases hb5 : c.b5 with
          | false =>
            cases hb1 : c.b1 with
            | false =>
              cases hb7 : c.b7 with
              | false =>
                cases hb8 : c.b8 with
                | false =>
                  cases hb4 : c.b4 with
                  | false =>
                    cases hb6 : c.b6 with
                    | false =>
                      exact (F9 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G9 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      cases hb10 : c.b10 with
                      | false =>
                        exact (F10 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G10 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        exact (F11 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G11 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    cases hb12 : c.b12 with
                    | false =>
                      exact (F12 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G12 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      exact (F13 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G13 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb12 : c.b12 with
                  | false =>
                    cases hb3 : c.b3 with
                    | false =>
                      exact (F14 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G14 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      exact (F15 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G15 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F16 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G16 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F17 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G17 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb10 : c.b10 with
              | false =>
                cases hb6 : c.b6 with
                | false =>
                  exact (F18 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G18 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F19 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G19 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb7 : c.b7 with
                | false =>
                  cases hb9 : c.b9 with
                  | false =>
                    exact (F20 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G20 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F21 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G21 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F22 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G22 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            cases hb9 : c.b9 with
            | false =>
              cases hb4 : c.b4 with
              | false =>
                cases hb8 : c.b8 with
                | false =>
                  cases hb1 : c.b1 with
                  | false =>
                    exact (F23 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G23 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F24 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G24 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F25 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G25 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb8 : c.b8 with
                | false =>
                  cases hb6 : c.b6 with
                  | false =>
                    exact (F26 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G26 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F27 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G27 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb1 : c.b1 with
                  | false =>
                    exact (F28 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G28 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F29 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G29 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb10 : c.b10 with
              | false =>
                cases hb3 : c.b3 with
                | false =>
                  exact (F30 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G30 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb1 : c.b1 with
                  | false =>
                    exact (F31 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G31 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F32 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G32 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F33 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G33 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
        | true =>
          cases hb5 : c.b5 with
          | false =>
            cases hb12 : c.b12 with
            | false =>
              cases hb8 : c.b8 with
              | false =>
                cases hb4 : c.b4 with
                | false =>
                  exact (F34 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G34 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F35 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G35 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F36 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G36 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb9 : c.b9 with
              | false =>
                cases hb7 : c.b7 with
                | false =>
                  exact (F37 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G37 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb8 : c.b8 with
                  | false =>
                    exact (F38 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G38 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F39 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G39 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F40 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G40 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            cases hb8 : c.b8 with
            | false =>
              exact (F41 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G41 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb10 : c.b10 with
              | false =>
                exact (F42 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G42 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F43 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G43 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
      | true =>
        cases hb6 : c.b6 with
        | false =>
          exact (F44 c (by assumption) (by assumption) (by assumption) (by assumption)).trans (G44 c (by assumption) (by assumption) (by assumption) (by assumption)).symm
        | true =>
          cases hb12 : c.b12 with
          | false =>
            cases hb7 : c.b7 with
            | false =>
              cases hb0 : c.b0 with
              | false =>
                cases hb3 : c.b3 with
                | false =>
                  cases hb4 : c.b4 with
                  | false =>
                    cases hb10 : c.b10 with
                    | false =>
                      cases hb1 : c.b1 with
                      | false =>
                        cases hb5 : c.b5 with
                        | false =>
                          exact (F45 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G45 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F46 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G46 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        exact (F47 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G47 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      cases hb1 : c.b1 with
                      | false =>
                        cases hb5 : c.b5 with
                        | false =>
                          cases hb8 : c.b8 with
                          | false =>
                            exact (F48 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G48 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                          | true =>
                            exact (F49 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G49 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          cases hb8 : c.b8 with
                          | false =>
                            exact (F50 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G50 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                          | true =>
                            exact (F51 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G51 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        cases hb5 : c.b5 with
                        | false =>
                          exact (F52 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G52 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F53 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G53 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    cases hb8 : c.b8 with
                    | false =>
                      exact (F54 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G54 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      exact (F55 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G55 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb10 : c.b10 with
                  | false =>
                    exact (F56 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G56 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F57 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G57 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb1 : c.b1 with
                | false =>
                  exact (F58 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G58 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F59 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G59 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb4 : c.b4 with
              | false =>
                cases hb0 : c.b0 with
                | false =>
                  cases hb10 : c.b10 with
                  | false =>
                    exact (F60 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G60 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    cases hb8 : c.b8 with
                    | false =>
                      exact (F61 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G61 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      exact (F62 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G62 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb1 : c.b1 with
                  | false =>
                    exact (F63 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G63 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F64 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G64 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb1 : c.b1 with
                | false =>
                  cases hb10 : c.b10 with
                  | false =>
                    cases hb8 : c.b8 with
                    | false =>
                      exact (F65 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G65 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      cases hb9 : c.b9 with
                      | false =>
                        exact (F66 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G66 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        exact (F67 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G67 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F68 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G68 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb9 : c.b9 with
                  | false =>
                    exact (F69 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G69 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F70 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G70 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            cases hb8 : c.b8 with
            | false =>
              exact (F71 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G71 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              exact (F72 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G72 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
  | true =>
    cases hb4 : c.b4 with
    | false =>
      cases hb6 : c.b6 with
      | false =>
        exact (F73 c (by assumption) (by assumption) (by assumption)).trans (G73 c (by assumption) (by assumption) (by assumption)).symm
      | true =>
        cases hb7 : c.b7 with
        | false =>
          cases hb3 : c.b3 with
          | false =>
            exact (F74 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G74 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            exact (F75 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G75 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
        | true =>
          exact (F76 c (by assumption) (by assumption) (by assumption) (by assumption)).trans (G76 c (by assumption) (by assumption) (by assumption) (by assumption)).symm
    | true =>
      cases hb0 : c.b0 with
      | false =>
        cases hb6 : c.b6 with
        | false =>
          cases hb11 : c.b11 with
          | false =>
            cases hb13 : c.b13 with
            | false =>
              exact (F77 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G77 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb9 : c.b9 with
              | false =>
                cases hb3 : c.b3 with
                | false =>
                  exact (F78 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G78 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F79 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G79 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb8 : c.b8 with
                | false =>
                  cases hb7 : c.b7 with
                  | false =>
                    exact (F80 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G80 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F81 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G81 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb5 : c.b5 with
                  | false =>
                    cases hb10 : c.b10 with
                    | false =>
                      exact (F82 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G82 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      cases hb12 : c.b12 with
                      | false =>
                        cases hb1 : c.b1 with
                        | false =>
                          exact (F83 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G83 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F84 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G84 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        cases hb7 : c.b7 with
                        | false =>
                          exact (F85 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G85 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F86 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G86 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F87 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G87 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            cases hb3 : c.b3 with
            | false =>
              cases hb10 : c.b10 with
              | false =>
                cases hb9 : c.b9 with
                | false =>
                  cases hb12 : c.b12 with
                  | false =>
                    cases hb1 : c.b1 with
                    | false =>
                      exact (F88 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G88 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      exact (F89 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G89 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    cases hb5 : c.b5 with
                    | false =>
                      cases hb7 : c.b7 with
                      | false =>
                        exact (F90 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G90 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        exact (F91 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G91 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      cases hb8 : c.b8 with
                      | false =>
                        cases hb7 : c.b7 with
                        | false =>
                          exact (F92 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G92 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F93 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G93 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        cases hb13 : c.b13 with
                        | false =>
                          exact (F94 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G94 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F95 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G95 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb8 : c.b8 with
                  | false =>
                    exact (F96 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G96 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    cases hb1 : c.b1 with
                    | false =>
                      exact (F97 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G97 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      exact (F98 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G98 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb8 : c.b8 with
                | false =>
                  exact (F99 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G99 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F100 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G100 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb7 : c.b7 with
              | false =>
                cases hb1 : c.b1 with
                | false =>
                  cases hb12 : c.b12 with
                  | false =>
                    cases hb5 : c.b5 with
                    | false =>
                      cases hb9 : c.b9 with
                      | false =>
                        exact (F101 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G101 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        cases hb10 : c.b10 with
                        | false =>
                          exact (F102 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G102 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F103 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G103 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      exact (F104 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G104 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F105 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G105 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F106 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G106 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb13 : c.b13 with
                | false =>
                  exact (F107 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G107 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  cases hb1 : c.b1 with
                  | false =>
                    cases hb5 : c.b5 with
                    | false =>
                      exact (F108 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G108 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                    | true =>
                      cases hb8 : c.b8 with
                      | false =>
                        exact (F109 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G109 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                      | true =>
                        cases hb12 : c.b12 with
                        | false =>
                          cases hb9 : c.b9 with
                          | false =>
                            exact (F110 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G110 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                          | true =>
                            exact (F111 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G111 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                        | true =>
                          exact (F112 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G112 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                  | true =>
                    exact (F113 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G113 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
        | true =>
          exact (F114 c (by assumption) (by assumption) (by assumption) (by assumption)).trans (G114 c (by assumption) (by assumption) (by assumption) (by assumption)).symm
      | true =>
        cases hb9 : c.b9 with
        | false =>
          cases hb7 : c.b7 with
          | false =>
            cases hb12 : c.b12 with
            | false =>
              cases hb3 : c.b3 with
              | false =>
                exact (F115 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G115 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                cases hb1 : c.b1 with
                | false =>
                  exact (F116 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G116 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
                | true =>
                  exact (F117 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G117 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb8 : c.b8 with
              | false =>
                exact (F118 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G118 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F119 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G119 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            cases hb11 : c.b11 with
            | false =>
              cases hb12 : c.b12 with
              | false =>
                exact (F120 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G120 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F121 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G121 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              cases hb13 : c.b13 with
              | false =>
                exact (F122 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G122 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F123 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G123 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
        | true =>
          cases hb13 : c.b13 with
          | false =>
            cases hb11 : c.b11 with
            | false =>
              cases hb7 : c.b7 with
              | false =>
                exact (F124 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G124 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
              | true =>
                exact (F125 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G125 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
            | true =>
              exact (F126 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G126 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm
          | true =>
            exact (F127 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).trans (G127 c (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)).symm

end TblComplete
