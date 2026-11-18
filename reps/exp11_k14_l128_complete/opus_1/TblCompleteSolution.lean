import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127⟩ := hf
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45, k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63, k64, k65, k66, k67, k68, k69, k70, k71, k72, k73, k74, k75, k76, k77, k78, k79, k80, k81, k82, k83, k84, k85, k86, k87, k88, k89, k90, k91, k92, k93, k94, k95, k96, k97, k98, k99, k100, k101, k102, k103, k104, k105, k106, k107, k108, k109, k110, k111, k112, k113, k114, k115, k116, k117, k118, k119, k120, k121, k122, k123, k124, k125, k126, k127⟩ := hg
  cases hb2 : c.b2
  · 
    cases hb13 : c.b13
    · 
      cases hb5 : c.b5
      · 
        cases hb9 : c.b9
        · 
          exact (h0 c hb2 hb13 hb5 hb9).trans (k0 c hb2 hb13 hb5 hb9).symm
        · 
          exact (h1 c hb2 hb13 hb5 hb9).trans (k1 c hb2 hb13 hb5 hb9).symm
      · 
        cases hb8 : c.b8
        · 
          cases hb1 : c.b1
          · 
            exact (h2 c hb2 hb13 hb5 hb8 hb1).trans (k2 c hb2 hb13 hb5 hb8 hb1).symm
          · 
            exact (h3 c hb2 hb13 hb5 hb8 hb1).trans (k3 c hb2 hb13 hb5 hb8 hb1).symm
        · 
          cases hb9 : c.b9
          · 
            cases hb0 : c.b0
            · 
              cases hb12 : c.b12
              · 
                cases hb10 : c.b10
                · 
                  exact (h4 c hb2 hb13 hb5 hb8 hb9 hb0 hb12 hb10).trans (k4 c hb2 hb13 hb5 hb8 hb9 hb0 hb12 hb10).symm
                · 
                  exact (h5 c hb2 hb13 hb5 hb8 hb9 hb0 hb12 hb10).trans (k5 c hb2 hb13 hb5 hb8 hb9 hb0 hb12 hb10).symm
              · 
                exact (h6 c hb2 hb13 hb5 hb8 hb9 hb0 hb12).trans (k6 c hb2 hb13 hb5 hb8 hb9 hb0 hb12).symm
            · 
              exact (h7 c hb2 hb13 hb5 hb8 hb9 hb0).trans (k7 c hb2 hb13 hb5 hb8 hb9 hb0).symm
          · 
            exact (h8 c hb2 hb13 hb5 hb8 hb9).trans (k8 c hb2 hb13 hb5 hb8 hb9).symm
    · 
      cases hb11 : c.b11
      · 
        cases hb0 : c.b0
        · 
          cases hb5 : c.b5
          · 
            cases hb1 : c.b1
            · 
              cases hb7 : c.b7
              · 
                cases hb8 : c.b8
                · 
                  cases hb4 : c.b4
                  · 
                    cases hb6 : c.b6
                    · 
                      exact (h9 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb6).trans (k9 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb6).symm
                    · 
                      cases hb10 : c.b10
                      · 
                        exact (h10 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb6 hb10).trans (k10 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb6 hb10).symm
                      · 
                        exact (h11 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb6 hb10).trans (k11 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb6 hb10).symm
                  · 
                    cases hb12 : c.b12
                    · 
                      exact (h12 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb12).trans (k12 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb12).symm
                    · 
                      exact (h13 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb12).trans (k13 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb4 hb12).symm
                · 
                  cases hb12 : c.b12
                  · 
                    cases hb3 : c.b3
                    · 
                      exact (h14 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb12 hb3).trans (k14 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb12 hb3).symm
                    · 
                      exact (h15 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb12 hb3).trans (k15 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb12 hb3).symm
                  · 
                    exact (h16 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb12).trans (k16 c hb2 hb13 hb11 hb0 hb5 hb1 hb7 hb8 hb12).symm
              · 
                exact (h17 c hb2 hb13 hb11 hb0 hb5 hb1 hb7).trans (k17 c hb2 hb13 hb11 hb0 hb5 hb1 hb7).symm
            · 
              cases hb10 : c.b10
              · 
                cases hb6 : c.b6
                · 
                  exact (h18 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb6).trans (k18 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb6).symm
                · 
                  exact (h19 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb6).trans (k19 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb6).symm
              · 
                cases hb7 : c.b7
                · 
                  cases hb9 : c.b9
                  · 
                    exact (h20 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb7 hb9).trans (k20 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb7 hb9).symm
                  · 
                    exact (h21 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb7 hb9).trans (k21 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb7 hb9).symm
                · 
                  exact (h22 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb7).trans (k22 c hb2 hb13 hb11 hb0 hb5 hb1 hb10 hb7).symm
          · 
            cases hb9 : c.b9
            · 
              cases hb4 : c.b4
              · 
                cases hb8 : c.b8
                · 
                  cases hb1 : c.b1
                  · 
                    exact (h23 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).trans (k23 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).symm
                  · 
                    exact (h24 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).trans (k24 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).symm
                · 
                  exact (h25 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8).trans (k25 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8).symm
              · 
                cases hb8 : c.b8
                · 
                  cases hb6 : c.b6
                  · 
                    exact (h26 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb6).trans (k26 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb6).symm
                  · 
                    exact (h27 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb6).trans (k27 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb6).symm
                · 
                  cases hb1 : c.b1
                  · 
                    exact (h28 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).trans (k28 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).symm
                  · 
                    exact (h29 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).trans (k29 c hb2 hb13 hb11 hb0 hb5 hb9 hb4 hb8 hb1).symm
            · 
              cases hb10 : c.b10
              · 
                cases hb3 : c.b3
                · 
                  exact (h30 c hb2 hb13 hb11 hb0 hb5 hb9 hb10 hb3).trans (k30 c hb2 hb13 hb11 hb0 hb5 hb9 hb10 hb3).symm
                · 
                  cases hb1 : c.b1
                  · 
                    exact (h31 c hb2 hb13 hb11 hb0 hb5 hb9 hb10 hb3 hb1).trans (k31 c hb2 hb13 hb11 hb0 hb5 hb9 hb10 hb3 hb1).symm
                  · 
                    exact (h32 c hb2 hb13 hb11 hb0 hb5 hb9 hb10 hb3 hb1).trans (k32 c hb2 hb13 hb11 hb0 hb5 hb9 hb10 hb3 hb1).symm
              · 
                exact (h33 c hb2 hb13 hb11 hb0 hb5 hb9 hb10).trans (k33 c hb2 hb13 hb11 hb0 hb5 hb9 hb10).symm
        · 
          cases hb5 : c.b5
          · 
            cases hb12 : c.b12
            · 
              cases hb8 : c.b8
              · 
                cases hb4 : c.b4
                · 
                  exact (h34 c hb2 hb13 hb11 hb0 hb5 hb12 hb8 hb4).trans (k34 c hb2 hb13 hb11 hb0 hb5 hb12 hb8 hb4).symm
                · 
                  exact (h35 c hb2 hb13 hb11 hb0 hb5 hb12 hb8 hb4).trans (k35 c hb2 hb13 hb11 hb0 hb5 hb12 hb8 hb4).symm
              · 
                exact (h36 c hb2 hb13 hb11 hb0 hb5 hb12 hb8).trans (k36 c hb2 hb13 hb11 hb0 hb5 hb12 hb8).symm
            · 
              cases hb9 : c.b9
              · 
                cases hb7 : c.b7
                · 
                  exact (h37 c hb2 hb13 hb11 hb0 hb5 hb12 hb9 hb7).trans (k37 c hb2 hb13 hb11 hb0 hb5 hb12 hb9 hb7).symm
                · 
                  cases hb8 : c.b8
                  · 
                    exact (h38 c hb2 hb13 hb11 hb0 hb5 hb12 hb9 hb7 hb8).trans (k38 c hb2 hb13 hb11 hb0 hb5 hb12 hb9 hb7 hb8).symm
                  · 
                    exact (h39 c hb2 hb13 hb11 hb0 hb5 hb12 hb9 hb7 hb8).trans (k39 c hb2 hb13 hb11 hb0 hb5 hb12 hb9 hb7 hb8).symm
              · 
                exact (h40 c hb2 hb13 hb11 hb0 hb5 hb12 hb9).trans (k40 c hb2 hb13 hb11 hb0 hb5 hb12 hb9).symm
          · 
            cases hb8 : c.b8
            · 
              exact (h41 c hb2 hb13 hb11 hb0 hb5 hb8).trans (k41 c hb2 hb13 hb11 hb0 hb5 hb8).symm
            · 
              cases hb10 : c.b10
              · 
                exact (h42 c hb2 hb13 hb11 hb0 hb5 hb8 hb10).trans (k42 c hb2 hb13 hb11 hb0 hb5 hb8 hb10).symm
              · 
                exact (h43 c hb2 hb13 hb11 hb0 hb5 hb8 hb10).trans (k43 c hb2 hb13 hb11 hb0 hb5 hb8 hb10).symm
      · 
        cases hb6 : c.b6
        · 
          exact (h44 c hb2 hb13 hb11 hb6).trans (k44 c hb2 hb13 hb11 hb6).symm
        · 
          cases hb12 : c.b12
          · 
            cases hb7 : c.b7
            · 
              cases hb0 : c.b0
              · 
                cases hb3 : c.b3
                · 
                  cases hb4 : c.b4
                  · 
                    cases hb10 : c.b10
                    · 
                      cases hb1 : c.b1
                      · 
                        cases hb5 : c.b5
                        · 
                          exact (h45 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).trans (k45 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).symm
                        · 
                          exact (h46 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).trans (k46 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).symm
                      · 
                        exact (h47 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1).trans (k47 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1).symm
                    · 
                      cases hb1 : c.b1
                      · 
                        cases hb5 : c.b5
                        · 
                          cases hb8 : c.b8
                          · 
                            exact (h48 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).trans (k48 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).symm
                          · 
                            exact (h49 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).trans (k49 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).symm
                        · 
                          cases hb8 : c.b8
                          · 
                            exact (h50 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).trans (k50 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).symm
                          · 
                            exact (h51 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).trans (k51 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5 hb8).symm
                      · 
                        cases hb5 : c.b5
                        · 
                          exact (h52 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).trans (k52 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).symm
                        · 
                          exact (h53 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).trans (k53 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb10 hb1 hb5).symm
                  · 
                    cases hb8 : c.b8
                    · 
                      exact (h54 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb8).trans (k54 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb8).symm
                    · 
                      exact (h55 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb8).trans (k55 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb4 hb8).symm
                · 
                  cases hb10 : c.b10
                  · 
                    exact (h56 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb10).trans (k56 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb10).symm
                  · 
                    exact (h57 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb10).trans (k57 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb3 hb10).symm
              · 
                cases hb1 : c.b1
                · 
                  exact (h58 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb1).trans (k58 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb1).symm
                · 
                  exact (h59 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb1).trans (k59 c hb2 hb13 hb11 hb6 hb12 hb7 hb0 hb1).symm
            · 
              cases hb4 : c.b4
              · 
                cases hb0 : c.b0
                · 
                  cases hb10 : c.b10
                  · 
                    exact (h60 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb10).trans (k60 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb10).symm
                  · 
                    cases hb8 : c.b8
                    · 
                      exact (h61 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb10 hb8).trans (k61 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb10 hb8).symm
                    · 
                      exact (h62 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb10 hb8).trans (k62 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb10 hb8).symm
                · 
                  cases hb1 : c.b1
                  · 
                    exact (h63 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb1).trans (k63 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb1).symm
                  · 
                    exact (h64 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb1).trans (k64 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb0 hb1).symm
              · 
                cases hb1 : c.b1
                · 
                  cases hb10 : c.b10
                  · 
                    cases hb8 : c.b8
                    · 
                      exact (h65 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10 hb8).trans (k65 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10 hb8).symm
                    · 
                      cases hb9 : c.b9
                      · 
                        exact (h66 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10 hb8 hb9).trans (k66 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10 hb8 hb9).symm
                      · 
                        exact (h67 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10 hb8 hb9).trans (k67 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10 hb8 hb9).symm
                  · 
                    exact (h68 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10).trans (k68 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb10).symm
                · 
                  cases hb9 : c.b9
                  · 
                    exact (h69 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb9).trans (k69 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb9).symm
                  · 
                    exact (h70 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb9).trans (k70 c hb2 hb13 hb11 hb6 hb12 hb7 hb4 hb1 hb9).symm
          · 
            cases hb8 : c.b8
            · 
              exact (h71 c hb2 hb13 hb11 hb6 hb12 hb8).trans (k71 c hb2 hb13 hb11 hb6 hb12 hb8).symm
            · 
              exact (h72 c hb2 hb13 hb11 hb6 hb12 hb8).trans (k72 c hb2 hb13 hb11 hb6 hb12 hb8).symm
  · 
    cases hb4 : c.b4
    · 
      cases hb6 : c.b6
      · 
        exact (h73 c hb2 hb4 hb6).trans (k73 c hb2 hb4 hb6).symm
      · 
        cases hb7 : c.b7
        · 
          cases hb3 : c.b3
          · 
            exact (h74 c hb2 hb4 hb6 hb7 hb3).trans (k74 c hb2 hb4 hb6 hb7 hb3).symm
          · 
            exact (h75 c hb2 hb4 hb6 hb7 hb3).trans (k75 c hb2 hb4 hb6 hb7 hb3).symm
        · 
          exact (h76 c hb2 hb4 hb6 hb7).trans (k76 c hb2 hb4 hb6 hb7).symm
    · 
      cases hb0 : c.b0
      · 
        cases hb6 : c.b6
        · 
          cases hb11 : c.b11
          · 
            cases hb13 : c.b13
            · 
              exact (h77 c hb2 hb4 hb0 hb6 hb11 hb13).trans (k77 c hb2 hb4 hb0 hb6 hb11 hb13).symm
            · 
              cases hb9 : c.b9
              · 
                cases hb3 : c.b3
                · 
                  exact (h78 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb3).trans (k78 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb3).symm
                · 
                  exact (h79 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb3).trans (k79 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb3).symm
              · 
                cases hb8 : c.b8
                · 
                  cases hb7 : c.b7
                  · 
                    exact (h80 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb7).trans (k80 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb7).symm
                  · 
                    exact (h81 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb7).trans (k81 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb7).symm
                · 
                  cases hb5 : c.b5
                  · 
                    cases hb10 : c.b10
                    · 
                      exact (h82 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10).trans (k82 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10).symm
                    · 
                      cases hb12 : c.b12
                      · 
                        cases hb1 : c.b1
                        · 
                          exact (h83 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb1).trans (k83 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb1).symm
                        · 
                          exact (h84 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb1).trans (k84 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb1).symm
                      · 
                        cases hb7 : c.b7
                        · 
                          exact (h85 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb7).trans (k85 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb7).symm
                        · 
                          exact (h86 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb7).trans (k86 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5 hb10 hb12 hb7).symm
                  · 
                    exact (h87 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5).trans (k87 c hb2 hb4 hb0 hb6 hb11 hb13 hb9 hb8 hb5).symm
          · 
            cases hb3 : c.b3
            · 
              cases hb10 : c.b10
              · 
                cases hb9 : c.b9
                · 
                  cases hb12 : c.b12
                  · 
                    cases hb1 : c.b1
                    · 
                      exact (h88 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb1).trans (k88 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb1).symm
                    · 
                      exact (h89 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb1).trans (k89 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb1).symm
                  · 
                    cases hb5 : c.b5
                    · 
                      cases hb7 : c.b7
                      · 
                        exact (h90 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb7).trans (k90 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb7).symm
                      · 
                        exact (h91 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb7).trans (k91 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb7).symm
                    · 
                      cases hb8 : c.b8
                      · 
                        cases hb7 : c.b7
                        · 
                          exact (h92 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb7).trans (k92 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb7).symm
                        · 
                          exact (h93 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb7).trans (k93 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb7).symm
                      · 
                        cases hb13 : c.b13
                        · 
                          exact (h94 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb13).trans (k94 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb13).symm
                        · 
                          exact (h95 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb13).trans (k95 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb12 hb5 hb8 hb13).symm
                · 
                  cases hb8 : c.b8
                  · 
                    exact (h96 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb8).trans (k96 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb8).symm
                  · 
                    cases hb1 : c.b1
                    · 
                      exact (h97 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb8 hb1).trans (k97 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb8 hb1).symm
                    · 
                      exact (h98 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb8 hb1).trans (k98 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb9 hb8 hb1).symm
              · 
                cases hb8 : c.b8
                · 
                  exact (h99 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb8).trans (k99 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb8).symm
                · 
                  exact (h100 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb8).trans (k100 c hb2 hb4 hb0 hb6 hb11 hb3 hb10 hb8).symm
            · 
              cases hb7 : c.b7
              · 
                cases hb1 : c.b1
                · 
                  cases hb12 : c.b12
                  · 
                    cases hb5 : c.b5
                    · 
                      cases hb9 : c.b9
                      · 
                        exact (h101 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5 hb9).trans (k101 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5 hb9).symm
                      · 
                        cases hb10 : c.b10
                        · 
                          exact (h102 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5 hb9 hb10).trans (k102 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5 hb9 hb10).symm
                        · 
                          exact (h103 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5 hb9 hb10).trans (k103 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5 hb9 hb10).symm
                    · 
                      exact (h104 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5).trans (k104 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12 hb5).symm
                  · 
                    exact (h105 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12).trans (k105 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1 hb12).symm
                · 
                  exact (h106 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1).trans (k106 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb1).symm
              · 
                cases hb13 : c.b13
                · 
                  exact (h107 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13).trans (k107 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13).symm
                · 
                  cases hb1 : c.b1
                  · 
                    cases hb5 : c.b5
                    · 
                      exact (h108 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5).trans (k108 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5).symm
                    · 
                      cases hb8 : c.b8
                      · 
                        exact (h109 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8).trans (k109 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8).symm
                      · 
                        cases hb12 : c.b12
                        · 
                          cases hb9 : c.b9
                          · 
                            exact (h110 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8 hb12 hb9).trans (k110 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8 hb12 hb9).symm
                          · 
                            exact (h111 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8 hb12 hb9).trans (k111 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8 hb12 hb9).symm
                        · 
                          exact (h112 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8 hb12).trans (k112 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1 hb5 hb8 hb12).symm
                  · 
                    exact (h113 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1).trans (k113 c hb2 hb4 hb0 hb6 hb11 hb3 hb7 hb13 hb1).symm
        · 
          exact (h114 c hb2 hb4 hb0 hb6).trans (k114 c hb2 hb4 hb0 hb6).symm
      · 
        cases hb9 : c.b9
        · 
          cases hb7 : c.b7
          · 
            cases hb12 : c.b12
            · 
              cases hb3 : c.b3
              · 
                exact (h115 c hb2 hb4 hb0 hb9 hb7 hb12 hb3).trans (k115 c hb2 hb4 hb0 hb9 hb7 hb12 hb3).symm
              · 
                cases hb1 : c.b1
                · 
                  exact (h116 c hb2 hb4 hb0 hb9 hb7 hb12 hb3 hb1).trans (k116 c hb2 hb4 hb0 hb9 hb7 hb12 hb3 hb1).symm
                · 
                  exact (h117 c hb2 hb4 hb0 hb9 hb7 hb12 hb3 hb1).trans (k117 c hb2 hb4 hb0 hb9 hb7 hb12 hb3 hb1).symm
            · 
              cases hb8 : c.b8
              · 
                exact (h118 c hb2 hb4 hb0 hb9 hb7 hb12 hb8).trans (k118 c hb2 hb4 hb0 hb9 hb7 hb12 hb8).symm
              · 
                exact (h119 c hb2 hb4 hb0 hb9 hb7 hb12 hb8).trans (k119 c hb2 hb4 hb0 hb9 hb7 hb12 hb8).symm
          · 
            cases hb11 : c.b11
            · 
              cases hb12 : c.b12
              · 
                exact (h120 c hb2 hb4 hb0 hb9 hb7 hb11 hb12).trans (k120 c hb2 hb4 hb0 hb9 hb7 hb11 hb12).symm
              · 
                exact (h121 c hb2 hb4 hb0 hb9 hb7 hb11 hb12).trans (k121 c hb2 hb4 hb0 hb9 hb7 hb11 hb12).symm
            · 
              cases hb13 : c.b13
              · 
                exact (h122 c hb2 hb4 hb0 hb9 hb7 hb11 hb13).trans (k122 c hb2 hb4 hb0 hb9 hb7 hb11 hb13).symm
              · 
                exact (h123 c hb2 hb4 hb0 hb9 hb7 hb11 hb13).trans (k123 c hb2 hb4 hb0 hb9 hb7 hb11 hb13).symm
        · 
          cases hb13 : c.b13
          · 
            cases hb11 : c.b11
            · 
              cases hb7 : c.b7
              · 
                exact (h124 c hb2 hb4 hb0 hb9 hb13 hb11 hb7).trans (k124 c hb2 hb4 hb0 hb9 hb13 hb11 hb7).symm
              · 
                exact (h125 c hb2 hb4 hb0 hb9 hb13 hb11 hb7).trans (k125 c hb2 hb4 hb0 hb9 hb13 hb11 hb7).symm
            · 
              exact (h126 c hb2 hb4 hb0 hb9 hb13 hb11).trans (k126 c hb2 hb4 hb0 hb9 hb13 hb11).symm
          · 
            exact (h127 c hb2 hb4 hb0 hb9 hb13).trans (k127 c hb2 hb4 hb0 hb9 hb13).symm

end TblComplete
