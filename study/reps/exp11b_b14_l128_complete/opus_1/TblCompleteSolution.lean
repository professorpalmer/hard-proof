import Tbl
import TblLaws

open Tbl

namespace TblComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74, f75, f76, f77, f78, f79, f80, f81, f82, f83, f84, f85, f86, f87, f88, f89, f90, f91, f92, f93, f94, f95, f96, f97, f98, f99, f100, f101, f102, f103, f104, f105, f106, f107, f108, f109, f110, f111, f112, f113, f114, f115, f116, f117, f118, f119, f120, f121, f122, f123, f124, f125, f126, f127⟩ := hf
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, g98, g99, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119, g120, g121, g122, g123, g124, g125, g126, g127⟩ := hg
  cases h13 : c.b13
  · skip
    cases h0 : c.b0
    · skip
      cases h2 : c.b2
      · skip
        cases h4 : c.b4
        · skip
          cases h7 : c.b7
          · skip
            rw [f56 c h7 h2 h4 h0 h13, g56 c h7 h2 h4 h0 h13]
          · skip
            cases h5 : c.b5
            · skip
              rw [f91 c h2 h7 h5 h0 h13 h4, g91 c h2 h7 h5 h0 h13 h4]
            · skip
              rw [f54 c h7 h2 h13 h4 h5 h0, g54 c h7 h2 h13 h4 h5 h0]
        · skip
          cases h11 : c.b11
          · skip
            cases h12 : c.b12
            · skip
              rw [f93 c h0 h4 h2 h12 h11 h13, g93 c h0 h4 h2 h12 h11 h13]
            · skip
              rw [f84 c h13 h4 h12 h2 h0 h11, g84 c h13 h4 h12 h2 h0 h11]
          · skip
            rw [f66 c h2 h0 h13 h11 h4, g66 c h2 h0 h13 h11 h4]
      · skip
        cases h1 : c.b1
        · skip
          cases h10 : c.b10
          · skip
            cases h9 : c.b9
            · skip
              rw [f126 c h1 h13 h9 h10 h0 h2, g126 c h1 h13 h9 h10 h0 h2]
            · skip
              rw [f65 c h10 h13 h0 h1 h2 h9, g65 c h10 h13 h0 h1 h2 h9]
          · skip
            rw [f85 c h13 h10 h2 h0 h1, g85 c h13 h10 h2 h0 h1]
        · skip
          cases h5 : c.b5
          · skip
            rw [f42 c h5 h2 h1 h13 h0, g42 c h5 h2 h1 h13 h0]
          · skip
            cases h6 : c.b6
            · skip
              rw [f29 c h0 h2 h6 h1 h13 h5, g29 c h0 h2 h6 h1 h13 h5]
            · skip
              rw [f11 c h0 h5 h2 h1 h13 h6, g11 c h0 h5 h2 h1 h13 h6]
    · skip
      cases h9 : c.b9
      · skip
        cases h10 : c.b10
        · skip
          cases h11 : c.b11
          · skip
            cases h6 : c.b6
            · skip
              cases h8 : c.b8
              · skip
                cases h3 : c.b3
                · skip
                  cases h5 : c.b5
                  · skip
                    rw [f47 c h5 h3 h11 h8 h0 h10 h6 h13 h9, g47 c h5 h3 h11 h8 h0 h10 h6 h13 h9]
                  · skip
                    cases h7 : c.b7
                    · skip
                      rw [f63 c h11 h6 h13 h5 h9 h3 h10 h8 h7 h0, g63 c h11 h6 h13 h5 h9 h3 h10 h8 h7 h0]
                    · skip
                      rw [f81 c h7 h10 h0 h5 h11 h8 h13 h6 h9 h3, g81 c h7 h10 h0 h5 h11 h8 h13 h6 h9 h3]
                · skip
                  cases h7 : c.b7
                  · skip
                    rw [f77 c h7 h13 h9 h10 h6 h3 h8 h0 h11, g77 c h7 h13 h9 h10 h6 h3 h8 h0 h11]
                  · skip
                    rw [f6 c h11 h8 h6 h7 h3 h9 h10 h0 h13, g6 c h11 h8 h6 h7 h3 h9 h10 h0 h13]
              · skip
                cases h4 : c.b4
                · skip
                  cases h7 : c.b7
                  · skip
                    rw [f60 c h8 h9 h13 h10 h4 h6 h11 h7 h0, g60 c h8 h9 h13 h10 h4 h6 h11 h7 h0]
                  · skip
                    rw [f2 c h11 h10 h9 h0 h6 h7 h8 h4 h13, g2 c h11 h10 h9 h0 h6 h7 h8 h4 h13]
                · skip
                  cases h5 : c.b5
                  · skip
                    rw [f3 c h0 h9 h4 h13 h5 h10 h8 h11 h6, g3 c h0 h9 h4 h13 h5 h10 h8 h11 h6]
                  · skip
                    rw [f70 c h8 h0 h4 h11 h9 h5 h10 h6 h13, g70 c h8 h0 h4 h11 h9 h5 h10 h6 h13]
            · skip
              cases h8 : c.b8
              · skip
                cases h4 : c.b4
                · skip
                  rw [f110 c h0 h11 h10 h4 h9 h6 h8 h13, g110 c h0 h11 h10 h4 h9 h6 h8 h13]
                · skip
                  rw [f102 c h8 h4 h13 h11 h0 h6 h10 h9, g102 c h8 h4 h13 h11 h0 h6 h10 h9]
              · skip
                rw [f113 c h0 h8 h9 h6 h13 h11 h10, g113 c h0 h8 h9 h6 h13 h11 h10]
          · skip
            cases h3 : c.b3
            · skip
              cases h6 : c.b6
              · skip
                cases h5 : c.b5
                · skip
                  cases h4 : c.b4
                  · skip
                    cases h12 : c.b12
                    · skip
                      cases h7 : c.b7
                      · skip
                        cases h1 : c.b1
                        · skip
                          cases h2 : c.b2
                          · skip
                            cases h8 : c.b8
                            · skip
                              rw [f106 c h11 h6 h8 h10 h4 h3 h12 h1 h5 h9 h2 h13 h7 h0, g106 c h11 h6 h8 h10 h4 h3 h12 h1 h5 h9 h2 h13 h7 h0]
                            · skip
                              rw [f92 c h12 h5 h9 h13 h2 h3 h1 h11 h7 h10 h0 h6 h8 h4, g92 c h12 h5 h9 h13 h2 h3 h1 h11 h7 h10 h0 h6 h8 h4]
                          · skip
                            cases h8 : c.b8
                            · skip
                              rw [f69 c h6 h10 h1 h13 h7 h8 h9 h5 h0 h3 h12 h11 h2 h4, g69 c h6 h10 h1 h13 h7 h8 h9 h5 h0 h3 h12 h11 h2 h4]
                            · skip
                              rw [f0 c h12 h6 h1 h0 h4 h2 h5 h3 h10 h13 h9 h7 h8 h11, g0 c h12 h6 h1 h0 h4 h2 h5 h3 h10 h13 h9 h7 h8 h11]
                        · skip
                          cases h2 : c.b2
                          · skip
                            rw [f83 c h3 h10 h0 h4 h12 h7 h5 h2 h6 h1 h9 h11 h13, g83 c h3 h10 h0 h4 h12 h7 h5 h2 h6 h1 h9 h11 h13]
                          · skip
                            rw [f27 c h2 h0 h10 h12 h6 h9 h7 h3 h1 h13 h5 h11 h4, g27 c h2 h0 h10 h12 h6 h9 h7 h3 h1 h13 h5 h11 h4]
                      · skip
                        rw [f21 c h7 h10 h5 h11 h6 h0 h3 h12 h9 h4 h13, g21 c h7 h10 h5 h11 h6 h0 h3 h12 h9 h4 h13]
                    · skip
                      cases h2 : c.b2
                      · skip
                        rw [f25 c h11 h0 h10 h5 h12 h6 h13 h3 h4 h2 h9, g25 c h11 h0 h10 h5 h12 h6 h13 h3 h4 h2 h9]
                      · skip
                        rw [f116 c h0 h3 h10 h4 h9 h2 h11 h5 h13 h12 h6, g116 c h0 h3 h10 h4 h9 h2 h11 h5 h13 h12 h6]
                  · skip
                    rw [f8 c h0 h9 h3 h4 h13 h6 h10 h11 h5, g8 c h0 h9 h3 h4 h13 h6 h10 h11 h5]
                · skip
                  cases h2 : c.b2
                  · skip
                    cases h4 : c.b4
                    · skip
                      cases h7 : c.b7
                      · skip
                        rw [f46 c h13 h10 h0 h3 h6 h4 h2 h7 h9 h5 h11, g46 c h13 h10 h0 h3 h6 h4 h2 h7 h9 h5 h11]
                      · skip
                        cases h1 : c.b1
                        · skip
                          rw [f57 c h5 h3 h11 h10 h1 h2 h4 h6 h9 h0 h13 h7, g57 c h5 h3 h11 h10 h1 h2 h4 h6 h9 h0 h13 h7]
                        · skip
                          cases h8 : c.b8
                          · skip
                            cases h12 : c.b12
                            · skip
                              rw [f33 c h7 h0 h9 h13 h8 h4 h2 h11 h10 h3 h5 h1 h12 h6, g33 c h7 h0 h9 h13 h8 h4 h2 h11 h10 h3 h5 h1 h12 h6]
                            · skip
                              rw [f22 c h1 h2 h13 h8 h10 h4 h3 h6 h5 h7 h0 h9 h12 h11, g22 c h1 h2 h13 h8 h10 h4 h3 h6 h5 h7 h0 h9 h12 h11]
                          · skip
                            cases h12 : c.b12
                            · skip
                              rw [f62 c h8 h6 h10 h2 h5 h12 h3 h9 h0 h1 h7 h4 h13 h11, g62 c h8 h6 h10 h2 h5 h12 h3 h9 h0 h1 h7 h4 h13 h11]
                            · skip
                              rw [f97 c h9 h13 h8 h0 h2 h12 h6 h1 h10 h11 h5 h3 h4 h7, g97 c h9 h13 h8 h0 h2 h12 h6 h1 h10 h11 h5 h3 h4 h7]
                    · skip
                      cases h7 : c.b7
                      · skip
                        cases h12 : c.b12
                        · skip
                          rw [f37 c h2 h9 h3 h11 h0 h7 h5 h12 h13 h4 h10 h6, g37 c h2 h9 h3 h11 h0 h7 h5 h12 h13 h4 h10 h6]
                        · skip
                          cases h8 : c.b8
                          · skip
                            rw [f76 c h2 h7 h13 h9 h3 h11 h6 h4 h8 h12 h10 h5 h0, g76 c h2 h7 h13 h9 h3 h11 h6 h4 h8 h12 h10 h5 h0]
                          · skip
                            rw [f30 c h11 h0 h6 h12 h13 h7 h8 h9 h4 h10 h5 h3 h2, g30 c h11 h0 h6 h12 h13 h7 h8 h9 h4 h10 h5 h3 h2]
                      · skip
                        cases h1 : c.b1
                        · skip
                          rw [f13 c h11 h10 h6 h3 h5 h9 h1 h4 h13 h7 h2 h0, g13 c h11 h10 h6 h3 h5 h9 h1 h4 h13 h7 h2 h0]
                        · skip
                          cases h12 : c.b12
                          · skip
                            cases h8 : c.b8
                            · skip
                              rw [f96 c h7 h5 h2 h11 h12 h6 h9 h1 h10 h3 h8 h4 h0 h13, g96 c h7 h5 h2 h11 h12 h6 h9 h1 h10 h3 h8 h4 h0 h13]
                            · skip
                              rw [f35 c h11 h3 h8 h13 h7 h4 h12 h6 h1 h9 h2 h10 h5 h0, g35 c h11 h3 h8 h13 h7 h4 h12 h6 h1 h9 h2 h10 h5 h0]
                          · skip
                            cases h8 : c.b8
                            · skip
                              rw [f31 c h12 h11 h13 h1 h7 h0 h5 h10 h3 h4 h6 h2 h9 h8, g31 c h12 h11 h13 h1 h7 h0 h5 h10 h3 h4 h6 h2 h9 h8]
                            · skip
                              rw [f23 c h12 h0 h5 h13 h6 h11 h1 h10 h4 h7 h9 h8 h3 h2, g23 c h12 h0 h5 h13 h6 h11 h1 h10 h4 h7 h9 h8 h3 h2]
                  · skip
                    rw [f19 c h10 h11 h5 h13 h3 h0 h6 h2 h9, g19 c h10 h11 h5 h13 h3 h0 h6 h2 h9]
              · skip
                cases h7 : c.b7
                · skip
                  cases h12 : c.b12
                  · skip
                    rw [f32 c h11 h7 h6 h3 h10 h13 h0 h12 h9, g32 c h11 h7 h6 h3 h10 h13 h0 h12 h9]
                  · skip
                    cases h5 : c.b5
                    · skip
                      rw [f68 c h9 h6 h10 h13 h11 h7 h3 h0 h5 h12, g68 c h9 h6 h10 h13 h11 h7 h3 h0 h5 h12]
                    · skip
                      rw [f107 c h6 h13 h9 h10 h12 h7 h5 h0 h11 h3, g107 c h6 h13 h9 h10 h12 h7 h5 h0 h11 h3]
                · skip
                  rw [f43 c h10 h3 h6 h7 h0 h13 h11 h9, g43 c h10 h3 h6 h7 h0 h13 h11 h9]
            · skip
              cases h5 : c.b5
              · skip
                rw [f74 c h5 h0 h10 h13 h11 h3 h9, g74 c h5 h0 h10 h13 h11 h3 h9]
              · skip
                cases h4 : c.b4
                · skip
                  rw [f94 c h3 h0 h9 h4 h10 h13 h11 h5, g94 c h3 h0 h9 h4 h10 h13 h11 h5]
                · skip
                  rw [f52 c h11 h10 h0 h9 h3 h4 h13 h5, g52 c h11 h10 h0 h9 h3 h4 h13 h5]
        · skip
          cases h3 : c.b3
          · skip
            cases h11 : c.b11
            · skip
              rw [f87 c h10 h3 h13 h9 h0 h11, g87 c h10 h3 h13 h9 h0 h11]
            · skip
              rw [f61 c h13 h0 h11 h9 h10 h3, g61 c h13 h0 h11 h9 h10 h3]
          · skip
            rw [f75 c h10 h9 h13 h3 h0, g75 c h10 h9 h13 h3 h0]
      · skip
        cases h5 : c.b5
        · skip
          cases h12 : c.b12
          · skip
            cases h1 : c.b1
            · skip
              cases h4 : c.b4
              · skip
                cases h2 : c.b2
                · skip
                  cases h3 : c.b3
                  · skip
                    cases h7 : c.b7
                    · skip
                      rw [f67 c h0 h4 h9 h7 h2 h3 h5 h1 h12 h13, g67 c h0 h4 h9 h7 h2 h3 h5 h1 h12 h13]
                    · skip
                      rw [f123 c h3 h1 h7 h4 h2 h12 h5 h9 h0 h13, g123 c h3 h1 h7 h4 h2 h12 h5 h9 h0 h13]
                  · skip
                    cases h7 : c.b7
                    · skip
                      rw [f82 c h2 h13 h1 h7 h12 h3 h9 h4 h0 h5, g82 c h2 h13 h1 h7 h12 h3 h9 h4 h0 h5]
                    · skip
                      cases h8 : c.b8
                      · skip
                        rw [f41 c h9 h2 h5 h3 h12 h7 h4 h13 h1 h8 h0, g41 c h9 h2 h5 h3 h12 h7 h4 h13 h1 h8 h0]
                      · skip
                        rw [f48 c h1 h0 h12 h13 h2 h5 h3 h8 h4 h7 h9, g48 c h1 h0 h12 h13 h2 h5 h3 h8 h4 h7 h9]
                · skip
                  cases h3 : c.b3
                  · skip
                    cases h7 : c.b7
                    · skip
                      cases h10 : c.b10
                      · skip
                        cases h8 : c.b8
                        · skip
                          rw [f58 c h2 h4 h0 h1 h7 h5 h13 h3 h10 h8 h12 h9, g58 c h2 h4 h0 h1 h7 h5 h13 h3 h10 h8 h12 h9]
                        · skip
                          rw [f71 c h7 h0 h1 h5 h12 h8 h10 h2 h3 h9 h13 h4, g71 c h7 h0 h1 h5 h12 h8 h10 h2 h3 h9 h13 h4]
                      · skip
                        rw [f95 c h7 h0 h2 h13 h9 h10 h1 h12 h4 h5 h3, g95 c h7 h0 h2 h13 h9 h10 h1 h12 h4 h5 h3]
                    · skip
                      cases h11 : c.b11
                      · skip
                        rw [f78 c h13 h12 h5 h7 h3 h11 h4 h9 h1 h0 h2, g78 c h13 h12 h5 h7 h3 h11 h4 h9 h1 h0 h2]
                      · skip
                        rw [f101 c h12 h9 h13 h1 h2 h5 h11 h3 h4 h7 h0, g101 c h12 h9 h13 h1 h2 h5 h11 h3 h4 h7 h0]
                  · skip
                    rw [f12 c h1 h4 h0 h9 h5 h13 h2 h3 h12, g12 c h1 h4 h0 h9 h5 h13 h2 h3 h12]
              · skip
                rw [f5 c h1 h5 h9 h12 h0 h13 h4, g5 c h1 h5 h9 h12 h0 h13 h4]
            · skip
              cases h2 : c.b2
              · skip
                rw [f55 c h12 h1 h9 h0 h5 h2 h13, g55 c h12 h1 h9 h0 h5 h2 h13]
              · skip
                rw [f10 c h1 h12 h0 h9 h5 h2 h13, g10 c h1 h12 h0 h9 h5 h2 h13]
          · skip
            cases h4 : c.b4
            · skip
              rw [f112 c h13 h9 h12 h0 h4 h5, g112 c h13 h9 h12 h0 h4 h5]
            · skip
              cases h11 : c.b11
              · skip
                rw [f80 c h0 h11 h13 h12 h5 h4 h9, g80 c h0 h11 h13 h12 h5 h4 h9]
              · skip
                rw [f88 c h5 h9 h4 h12 h13 h11 h0, g88 c h5 h9 h4 h12 h13 h11 h0]
        · skip
          cases h8 : c.b8
          · skip
            cases h4 : c.b4
            · skip
              cases h11 : c.b11
              · skip
                cases h7 : c.b7
                · skip
                  rw [f64 c h8 h13 h5 h7 h4 h11 h9 h0, g64 c h8 h13 h5 h7 h4 h11 h9 h0]
                · skip
                  cases h1 : c.b1
                  · skip
                    cases h12 : c.b12
                    · skip
                      cases h3 : c.b3
                      · skip
                        rw [f90 c h0 h7 h1 h8 h5 h12 h13 h3 h11 h9 h4, g90 c h0 h7 h1 h8 h5 h12 h13 h3 h11 h9 h4]
                      · skip
                        cases h6 : c.b6
                        · skip
                          rw [f99 c h1 h6 h11 h0 h9 h7 h12 h4 h13 h5 h3 h8, g99 c h1 h6 h11 h0 h9 h7 h12 h4 h13 h5 h3 h8]
                        · skip
                          rw [f15 c h8 h7 h13 h9 h5 h12 h0 h11 h3 h6 h1 h4, g15 c h8 h7 h13 h9 h5 h12 h0 h11 h3 h6 h1 h4]
                    · skip
                      rw [f16 c h12 h13 h9 h5 h1 h7 h8 h4 h11 h0, g16 c h12 h13 h9 h5 h1 h7 h8 h4 h11 h0]
                  · skip
                    cases h12 : c.b12
                    · skip
                      rw [f111 c h7 h12 h1 h0 h13 h11 h9 h4 h8 h5, g111 c h7 h12 h1 h0 h13 h11 h9 h4 h8 h5]
                    · skip
                      rw [f4 c h9 h0 h13 h7 h1 h11 h8 h5 h12 h4, g4 c h9 h0 h13 h7 h1 h11 h8 h5 h12 h4]
              · skip
                cases h3 : c.b3
                · skip
                  cases h1 : c.b1
                  · skip
                    cases h2 : c.b2
                    · skip
                      rw [f103 c h1 h13 h2 h4 h8 h5 h9 h3 h0 h11, g103 c h1 h13 h2 h4 h8 h5 h9 h3 h0 h11]
                    · skip
                      rw [f100 c h9 h11 h4 h2 h0 h3 h1 h8 h13 h5, g100 c h9 h11 h4 h2 h0 h3 h1 h8 h13 h5]
                  · skip
                    rw [f40 c h11 h8 h1 h9 h3 h13 h0 h4 h5, g40 c h11 h8 h1 h9 h3 h13 h0 h4 h5]
                · skip
                  cases h1 : c.b1
                  · skip
                    rw [f17 c h8 h5 h13 h3 h11 h4 h0 h1 h9, g17 c h8 h5 h13 h3 h11 h4 h0 h1 h9]
                  · skip
                    rw [f45 c h8 h0 h1 h4 h11 h5 h13 h3 h9, g45 c h8 h0 h1 h4 h11 h5 h13 h3 h9]
            · skip
              cases h12 : c.b12
              · skip
                rw [f7 c h0 h9 h5 h12 h4 h8 h13, g7 c h0 h9 h5 h12 h4 h8 h13]
              · skip
                rw [f49 c h12 h9 h5 h0 h8 h4 h13, g49 c h12 h9 h5 h0 h8 h4 h13]
          · skip
            cases h2 : c.b2
            · skip
              rw [f115 c h8 h9 h13 h0 h5 h2, g115 c h8 h9 h13 h0 h5 h2]
            · skip
              cases h11 : c.b11
              · skip
                cases h10 : c.b10
                · skip
                  cases h3 : c.b3
                  · skip
                    rw [f98 c h10 h13 h2 h5 h3 h0 h11 h9 h8, g98 c h10 h13 h2 h5 h3 h0 h11 h9 h8]
                  · skip
                    rw [f50 c h9 h13 h8 h0 h3 h11 h5 h10 h2, g50 c h9 h13 h8 h0 h3 h11 h5 h10 h2]
                · skip
                  cases h4 : c.b4
                  · skip
                    cases h7 : c.b7
                    · skip
                      cases h6 : c.b6
                      · skip
                        rw [f119 c h0 h8 h7 h10 h5 h11 h13 h9 h4 h6 h2, g119 c h0 h8 h7 h10 h5 h11 h13 h9 h4 h6 h2]
                      · skip
                        rw [f1 c h7 h11 h5 h6 h13 h4 h0 h9 h10 h8 h2, g1 c h7 h11 h5 h6 h13 h4 h0 h9 h10 h8 h2]
                    · skip
                      cases h12 : c.b12
                      · skip
                        cases h6 : c.b6
                        · skip
                          cases h3 : c.b3
                          · skip
                            rw [f79 c h0 h9 h5 h13 h7 h12 h3 h10 h6 h11 h8 h2 h4, g79 c h0 h9 h5 h13 h7 h12 h3 h10 h6 h11 h8 h2 h4]
                          · skip
                            rw [f104 c h12 h10 h11 h0 h7 h6 h2 h3 h8 h4 h5 h9 h13, g104 c h12 h10 h11 h0 h7 h6 h2 h3 h8 h4 h5 h9 h13]
                        · skip
                          rw [f105 c h8 h12 h10 h6 h4 h13 h5 h0 h2 h9 h11 h7, g105 c h8 h12 h10 h6 h4 h13 h5 h0 h2 h9 h11 h7]
                      · skip
                        rw [f120 c h8 h5 h11 h12 h7 h2 h10 h13 h0 h4 h9, g120 c h8 h5 h11 h12 h7 h2 h10 h13 h0 h4 h9]
                  · skip
                    cases h6 : c.b6
                    · skip
                      cases h12 : c.b12
                      · skip
                        cases h7 : c.b7
                        · skip
                          rw [f34 c h5 h7 h2 h13 h11 h6 h12 h0 h8 h4 h9 h10, g34 c h5 h7 h2 h13 h11 h6 h12 h0 h8 h4 h9 h10]
                        · skip
                          rw [f28 c h13 h6 h8 h11 h9 h7 h5 h10 h12 h2 h4 h0, g28 c h13 h6 h8 h11 h9 h7 h5 h10 h12 h2 h4 h0]
                      · skip
                        cases h1 : c.b1
                        · skip
                          cases h3 : c.b3
                          · skip
                            rw [f117 c h1 h2 h0 h13 h5 h4 h6 h3 h11 h12 h8 h10 h9, g117 c h1 h2 h0 h13 h5 h4 h6 h3 h11 h12 h8 h10 h9]
                          · skip
                            cases h7 : c.b7
                            · skip
                              rw [f20 c h13 h11 h0 h7 h2 h10 h6 h12 h8 h9 h5 h4 h3 h1, g20 c h13 h11 h0 h7 h2 h10 h6 h12 h8 h9 h5 h4 h3 h1]
                            · skip
                              rw [f89 c h8 h13 h5 h12 h3 h6 h10 h1 h4 h9 h2 h11 h0 h7, g89 c h8 h13 h5 h12 h3 h6 h10 h1 h4 h9 h2 h11 h0 h7]
                        · skip
                          cases h7 : c.b7
                          · skip
                            cases h3 : c.b3
                            · skip
                              rw [f53 c h2 h13 h5 h11 h12 h7 h9 h4 h10 h3 h8 h0 h1 h6, g53 c h2 h13 h5 h11 h12 h7 h9 h4 h10 h3 h8 h0 h1 h6]
                            · skip
                              rw [f127 c h5 h13 h7 h3 h2 h9 h4 h6 h1 h11 h10 h12 h8 h0, g127 c h5 h13 h7 h3 h2 h9 h4 h6 h1 h11 h10 h12 h8 h0]
                          · skip
                            cases h3 : c.b3
                            · skip
                              rw [f18 c h7 h11 h9 h2 h0 h1 h3 h12 h4 h6 h8 h10 h5 h13, g18 c h7 h11 h9 h2 h0 h1 h3 h12 h4 h6 h8 h10 h5 h13]
                            · skip
                              rw [f38 c h3 h10 h4 h8 h2 h0 h6 h7 h9 h11 h13 h1 h5 h12, g38 c h3 h10 h4 h8 h2 h0 h6 h7 h9 h11 h13 h1 h5 h12]
                    · skip
                      rw [f51 c h13 h6 h10 h11 h9 h8 h2 h5 h0 h4, g51 c h13 h6 h10 h11 h9 h8 h2 h5 h0 h4]
              · skip
                cases h10 : c.b10
                · skip
                  cases h7 : c.b7
                  · skip
                    cases h6 : c.b6
                    · skip
                      cases h3 : c.b3
                      · skip
                        rw [f14 c h5 h11 h10 h9 h0 h8 h7 h6 h3 h13 h2, g14 c h5 h11 h10 h9 h0 h8 h7 h6 h3 h13 h2]
                      · skip
                        rw [f9 c h0 h9 h3 h13 h6 h2 h8 h10 h11 h5 h7, g9 c h0 h9 h3 h13 h6 h2 h8 h10 h11 h5 h7]
                    · skip
                      rw [f36 c h13 h2 h8 h6 h7 h5 h0 h11 h10 h9, g36 c h13 h2 h8 h6 h7 h5 h0 h11 h10 h9]
                  · skip
                    cases h1 : c.b1
                    · skip
                      rw [f108 c h13 h11 h0 h2 h10 h8 h9 h5 h1 h7, g108 c h13 h11 h0 h2 h10 h8 h9 h5 h1 h7]
                    · skip
                      cases h6 : c.b6
                      · skip
                        cases h4 : c.b4
                        · skip
                          rw [f118 c h13 h11 h4 h8 h6 h10 h9 h0 h7 h1 h5 h2, g118 c h13 h11 h4 h8 h6 h10 h9 h0 h7 h1 h5 h2]
                        · skip
                          cases h3 : c.b3
                          · skip
                            rw [f124 c h7 h8 h3 h9 h5 h2 h13 h4 h11 h0 h1 h10 h6, g124 c h7 h8 h3 h9 h5 h2 h13 h4 h11 h0 h1 h10 h6]
                          · skip
                            rw [f109 c h0 h1 h13 h4 h3 h8 h10 h7 h6 h9 h11 h2 h5, g109 c h0 h1 h13 h4 h3 h8 h10 h7 h6 h9 h11 h2 h5]
                      · skip
                        rw [f24 c h7 h8 h1 h5 h11 h10 h13 h6 h9 h0 h2, g24 c h7 h8 h1 h5 h11 h10 h13 h6 h9 h0 h2]
                · skip
                  cases h7 : c.b7
                  · skip
                    cases h1 : c.b1
                    · skip
                      cases h4 : c.b4
                      · skip
                        rw [f26 c h13 h1 h4 h10 h5 h11 h8 h0 h7 h2 h9, g26 c h13 h1 h4 h10 h5 h11 h8 h0 h7 h2 h9]
                      · skip
                        rw [f72 c h10 h13 h4 h8 h11 h0 h1 h7 h9 h2 h5, g72 c h10 h13 h4 h8 h11 h0 h1 h7 h9 h2 h5]
                    · skip
                      cases h4 : c.b4
                      · skip
                        rw [f114 c h2 h8 h9 h7 h11 h1 h5 h4 h0 h13 h10, g114 c h2 h8 h9 h7 h11 h1 h5 h4 h0 h13 h10]
                      · skip
                        rw [f86 c h1 h10 h13 h9 h8 h11 h5 h0 h2 h7 h4, g86 c h1 h10 h13 h9 h8 h11 h5 h0 h2 h7 h4]
                  · skip
                    rw [f125 c h11 h9 h0 h8 h7 h10 h5 h2 h13, g125 c h11 h9 h0 h8 h7 h10 h5 h2 h13]
  · skip
    cases h5 : c.b5
    · skip
      cases h12 : c.b12
      · skip
        cases h8 : c.b8
        · skip
          rw [f44 c h13 h5 h8 h12, g44 c h13 h5 h8 h12]
        · skip
          rw [f39 c h8 h13 h5 h12, g39 c h8 h13 h5 h12]
      · skip
        cases h10 : c.b10
        · skip
          cases h2 : c.b2
          · skip
            rw [f121 c h13 h12 h5 h10 h2, g121 c h13 h12 h5 h10 h2]
          · skip
            rw [f122 c h5 h12 h2 h13 h10, g122 c h5 h12 h2 h13 h10]
        · skip
          rw [f73 c h10 h13 h12 h5, g73 c h10 h13 h12 h5]
    · skip
      rw [f59 c h5 h13, g59 c h5 h13]

end TblComplete
