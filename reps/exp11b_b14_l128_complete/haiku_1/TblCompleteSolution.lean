/-
Hard Proof, experiment 11. Adversary solution: the completeness proof.

Claim: the laws are complete. The 128 law cubes partition the 14-bit case
space (checked by exhaustive count), so every case is fixed by one law.
Each case splits on its bits until one law's literals are all fixed.
-/
import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  unfold Passes at hf hg
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74, f75, f76, f77, f78, f79, f80, f81, f82, f83, f84, f85, f86, f87, f88, f89, f90, f91, f92, f93, f94, f95, f96, f97, f98, f99, f100, f101, f102, f103, f104, f105, f106, f107, f108, f109, f110, f111, f112, f113, f114, f115, f116, f117, f118, f119, f120, f121, f122, f123, f124, f125, f126, f127⟩ := hf
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, g98, g99, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119, g120, g121, g122, g123, g124, g125, g126, g127⟩ := hg
  rcases c with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩
  cases b12
  · cases b6
    · cases b1
      · cases b0
        · cases b8
          · cases b13
            · cases b7
              · cases b2
                · cases b4
                  · exact (f56 ⟨false, false, false, b3, false, b5, false, false, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, b5, false, false, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · exact (f93 ⟨false, false, false, b3, true, b5, false, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, b5, false, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, false, false, b3, true, b5, false, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, b5, false, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, b5, false, false, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, b5, false, false, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, b5, false, false, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, b5, false, false, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f85 ⟨false, false, true, b3, b4, b5, false, false, false, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, b5, false, false, false, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
              · cases b2
                · cases b4
                  · cases b5
                    · exact (f91 ⟨false, false, false, b3, false, false, false, true, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, false, true, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f54 ⟨false, false, false, b3, false, true, false, true, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, false, false, b3, false, true, false, true, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · exact (f93 ⟨false, false, false, b3, true, b5, false, true, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, b5, false, true, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, false, false, b3, true, b5, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, b5, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, b5, false, true, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, b5, false, true, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, b5, false, true, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, b5, false, true, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f85 ⟨false, false, true, b3, b4, b5, false, true, false, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, b5, false, true, false, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
            · cases b5
              · exact (f44 ⟨false, false, b2, b3, b4, false, false, b7, false, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, false, b2, b3, b4, false, false, b7, false, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
              · exact (f59 ⟨false, false, b2, b3, b4, true, false, b7, false, b9, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨false, false, b2, b3, b4, true, false, b7, false, b9, b10, b11, false, true⟩ rfl rfl).symm
          · cases b13
            · cases b7
              · cases b2
                · cases b4
                  · exact (f56 ⟨false, false, false, b3, false, b5, false, false, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, b5, false, false, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · exact (f93 ⟨false, false, false, b3, true, b5, false, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, b5, false, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, false, false, b3, true, b5, false, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, b5, false, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, b5, false, false, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, b5, false, false, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, b5, false, false, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, b5, false, false, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f85 ⟨false, false, true, b3, b4, b5, false, false, true, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, b5, false, false, true, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
              · cases b2
                · cases b4
                  · cases b5
                    · exact (f91 ⟨false, false, false, b3, false, false, false, true, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, false, true, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f54 ⟨false, false, false, b3, false, true, false, true, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, false, false, b3, false, true, false, true, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · exact (f93 ⟨false, false, false, b3, true, b5, false, true, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, b5, false, true, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, false, false, b3, true, b5, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, b5, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, b5, false, true, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, b5, false, true, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, b5, false, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, b5, false, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f85 ⟨false, false, true, b3, b4, b5, false, true, true, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, b5, false, true, true, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
            · cases b5
              · exact (f39 ⟨false, false, b2, b3, b4, false, false, b7, true, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, false, b2, b3, b4, false, false, b7, true, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
              · exact (f59 ⟨false, false, b2, b3, b4, true, false, b7, true, b9, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨false, false, b2, b3, b4, true, false, b7, true, b9, b10, b11, false, true⟩ rfl rfl).symm
        · cases b4
          · cases b2
            · cases b11
              · cases b10
                · cases b9
                  · cases b7
                    · cases b8
                      · cases b13
                        · cases b5
                          · cases b3
                            · exact (f47 ⟨true, false, false, false, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, false, false, false, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f77 ⟨true, false, false, true, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, false, false, true, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f63 ⟨true, false, false, false, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g63 ⟨true, false, false, false, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f77 ⟨true, false, false, true, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, false, false, true, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f44 ⟨true, false, false, b3, false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, b3, false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, false, b3, false, true, false, false, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, false, false, false, false, false, false, true⟩ rfl rfl).symm
                      · cases b13
                        · exact (f60 ⟨true, false, false, b3, false, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, false, false, b3, false, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f39 ⟨true, false, false, b3, false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, b3, false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, false, b3, false, true, false, false, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, false, true, false, false, false, false, true⟩ rfl rfl).symm
                    · cases b8
                      · cases b3
                        · cases b13
                          · cases b5
                            · exact (f47 ⟨true, false, false, false, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, false, false, false, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f81 ⟨true, false, false, false, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g81 ⟨true, false, false, false, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f44 ⟨true, false, false, false, false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, false, false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, false, false, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, false, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).symm
                        · cases b13
                          · exact (f6 ⟨true, false, false, true, false, b5, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, false, true, false, b5, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f44 ⟨true, false, false, true, false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, false, true, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, true, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).symm
                      · cases b13
                        · exact (f2 ⟨true, false, false, b3, false, b5, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g2 ⟨true, false, false, b3, false, b5, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f39 ⟨true, false, false, b3, false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, b3, false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, false, b3, false, true, false, true, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, true, true, false, false, false, false, true⟩ rfl rfl).symm
                  · cases b8
                    · cases b5
                      · cases b3
                        · cases b13
                          · cases b7
                            · exact (f67 ⟨true, false, false, false, false, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f44 ⟨true, false, false, false, false, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, false, false, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b7
                          · cases b13
                            · exact (f82 ⟨true, false, false, true, false, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, true, false, false, false, false, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, false, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f41 ⟨true, false, false, true, false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g41 ⟨true, false, false, true, false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, true, false, false, false, true, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, true, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b13
                        · cases b7
                          · exact (f64 ⟨true, false, false, b3, false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, false, false, b3, false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f90 ⟨true, false, false, false, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g90 ⟨true, false, false, false, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f99 ⟨true, false, false, true, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g99 ⟨true, false, false, true, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, false, b3, false, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b5
                        · cases b3
                          · cases b7
                            · exact (f67 ⟨true, false, false, false, false, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f82 ⟨true, false, false, true, false, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f48 ⟨true, false, false, true, false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g48 ⟨true, false, false, true, false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f115 ⟨true, false, false, b3, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, false, false, b3, false, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, b3, false, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, false, b3, false, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).symm
                · cases b8
                  · cases b9
                    · cases b13
                      · cases b3
                        · exact (f87 ⟨true, false, false, false, false, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, false, false, false, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, false, false, true, false, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f44 ⟨true, false, false, b3, false, false, false, b7, false, false, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, b3, false, false, false, b7, false, false, true, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, false, b3, false, true, false, b7, false, false, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, b7, false, false, true, false, false, true⟩ rfl rfl).symm
                    · cases b5
                      · cases b3
                        · cases b13
                          · cases b7
                            · exact (f67 ⟨true, false, false, false, false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f44 ⟨true, false, false, false, false, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, false, false, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b7
                          · cases b13
                            · exact (f82 ⟨true, false, false, true, false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, true, false, false, false, false, false, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, false, false, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f41 ⟨true, false, false, true, false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g41 ⟨true, false, false, true, false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, true, false, false, false, true, false, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, true, false, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b13
                        · cases b7
                          · exact (f64 ⟨true, false, false, b3, false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, false, false, b3, false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f90 ⟨true, false, false, false, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g90 ⟨true, false, false, false, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f99 ⟨true, false, false, true, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g99 ⟨true, false, false, true, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, false, b3, false, true, false, b7, false, true, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, b7, false, true, true, false, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b5
                      · cases b3
                        · cases b9
                          · exact (f87 ⟨true, false, false, false, false, false, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, false, false, false, false, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f67 ⟨true, false, false, false, false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b7
                          · cases b9
                            · exact (f75 ⟨true, false, false, true, false, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                            · exact (f82 ⟨true, false, false, true, false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b9
                            · exact (f75 ⟨true, false, false, true, false, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                            · exact (f48 ⟨true, false, false, true, false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g48 ⟨true, false, false, true, false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b9
                        · cases b3
                          · exact (f87 ⟨true, false, false, false, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, false, false, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, false, true, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f115 ⟨true, false, false, b3, false, true, false, b7, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, false, true, false, b7, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨true, false, false, b3, false, false, false, b7, true, b9, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, b3, false, false, false, b7, true, b9, true, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, false, b3, false, true, false, b7, true, b9, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, b7, true, b9, true, false, false, true⟩ rfl rfl).symm
              · cases b8
                · cases b5
                  · cases b7
                    · cases b13
                      · cases b9
                        · cases b10
                          · cases b3
                            · exact (f106 ⟨true, false, false, false, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g106 ⟨true, false, false, false, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f74 ⟨true, false, false, true, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f61 ⟨true, false, false, false, false, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, false, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, false, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · exact (f67 ⟨true, false, false, false, false, false, false, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, false, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f82 ⟨true, false, false, true, false, false, false, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, false, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨true, false, false, b3, false, false, false, false, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, b3, false, false, false, false, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b10
                      · cases b3
                        · cases b9
                          · cases b13
                            · exact (f21 ⟨true, false, false, false, false, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, false, false, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, false, false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, false, false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, false, false, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, false, false, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b9
                          · cases b13
                            · exact (f74 ⟨true, false, false, true, false, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, false, false, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, true, false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f41 ⟨true, false, false, true, false, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g41 ⟨true, false, false, true, false, false, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, true, false, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, true, false, true, false, true, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b9
                        · cases b13
                          · cases b3
                            · exact (f61 ⟨true, false, false, false, false, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, false, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, false, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f44 ⟨true, false, false, b3, false, false, false, true, false, false, true, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, b3, false, false, false, true, false, false, true, true, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b3
                          · cases b13
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, false, false, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, false, false, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f41 ⟨true, false, false, true, false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g41 ⟨true, false, false, true, false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, false, true, false, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, false, true, false, false, false, true, false, true, true, true, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b3
                      · cases b10
                        · cases b7
                          · cases b9
                            · exact (f46 ⟨true, false, false, false, false, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g46 ⟨true, false, false, false, false, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f103 ⟨true, false, false, false, false, true, false, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, false, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b9
                            · exact (f57 ⟨true, false, false, false, false, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g57 ⟨true, false, false, false, false, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f103 ⟨true, false, false, false, false, true, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, false, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b9
                          · exact (f61 ⟨true, false, false, false, false, true, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, true, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f103 ⟨true, false, false, false, false, true, false, b7, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, false, b7, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b9
                        · cases b10
                          · exact (f94 ⟨true, false, false, true, false, true, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, false, false, true, false, true, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, false, true, false, true, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, true, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f17 ⟨true, false, false, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, false, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, false, b3, false, true, false, b7, false, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, b7, false, b9, b10, true, false, true⟩ rfl rfl).symm
                · cases b7
                  · cases b13
                    · cases b10
                      · cases b3
                        · cases b9
                          · cases b5
                            · exact (f92 ⟨true, false, false, false, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g92 ⟨true, false, false, false, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f46 ⟨true, false, false, false, false, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g46 ⟨true, false, false, false, false, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f67 ⟨true, false, false, false, false, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f115 ⟨true, false, false, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · cases b9
                            · exact (f74 ⟨true, false, false, true, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f82 ⟨true, false, false, true, false, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b9
                            · exact (f94 ⟨true, false, false, true, false, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, false, false, true, false, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f115 ⟨true, false, false, true, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b9
                        · cases b3
                          · exact (f61 ⟨true, false, false, false, false, b5, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, b5, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, false, true, false, b5, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, b5, false, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · cases b5
                            · exact (f67 ⟨true, false, false, false, false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f115 ⟨true, false, false, false, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f82 ⟨true, false, false, true, false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f115 ⟨true, false, false, true, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨true, false, false, b3, false, false, false, false, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, b3, false, false, false, false, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, false, b3, false, true, false, false, true, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, false, true, b9, b10, true, false, true⟩ rfl rfl).symm
                  · cases b10
                    · cases b5
                      · cases b3
                        · cases b9
                          · cases b13
                            · exact (f21 ⟨true, false, false, false, false, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, false, false, false, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f39 ⟨true, false, false, false, false, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, false, false, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f39 ⟨true, false, false, false, false, false, false, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, false, false, false, false, true, true, true, false, true, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b13
                          · cases b9
                            · exact (f74 ⟨true, false, false, true, false, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, false, false, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f48 ⟨true, false, false, true, false, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g48 ⟨true, false, false, true, false, false, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f39 ⟨true, false, false, true, false, false, false, true, true, b9, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, true, false, false, false, true, true, b9, false, true, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b9
                          · cases b13
                            · exact (f57 ⟨true, false, false, false, false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g57 ⟨true, false, false, false, false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, false, false, false, true, false, true, true, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, false, false, true, false, true, true, false, false, true, false, true⟩ rfl rfl).symm
                          · cases b13
                            · exact (f115 ⟨true, false, false, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, false, false, false, true, false, true, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, false, false, true, false, true, true, true, false, true, false, true⟩ rfl rfl).symm
                        · cases b13
                          · cases b9
                            · exact (f94 ⟨true, false, false, true, false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, false, false, true, false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f115 ⟨true, false, false, true, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, false, true, false, true, false, true, true, b9, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, true, false, true, false, true, true, b9, false, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b5
                        · cases b3
                          · cases b9
                            · exact (f61 ⟨true, false, false, false, false, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f123 ⟨true, false, false, false, false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b9
                            · exact (f75 ⟨true, false, false, true, false, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                            · exact (f48 ⟨true, false, false, true, false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g48 ⟨true, false, false, true, false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b9
                          · cases b3
                            · exact (f61 ⟨true, false, false, false, false, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, false, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, true, false, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f115 ⟨true, false, false, b3, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, false, false, b3, false, false, false, true, true, b9, true, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, false, b3, false, false, false, true, true, b9, true, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, false, b3, false, true, false, true, true, b9, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, false, b3, false, true, false, true, true, b9, true, true, false, true⟩ rfl rfl).symm
            · cases b5
              · cases b3
                · cases b10
                  · cases b13
                    · cases b9
                      · cases b7
                        · cases b8
                          · cases b11
                            · exact (f47 ⟨true, false, true, false, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, false, true, false, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f69 ⟨true, false, true, false, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g69 ⟨true, false, true, false, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b11
                            · exact (f60 ⟨true, false, true, false, false, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, false, true, false, false, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f0 ⟨true, false, true, false, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g0 ⟨true, false, true, false, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · cases b8
                            · exact (f47 ⟨true, false, true, false, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, false, true, false, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f2 ⟨true, false, true, false, false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g2 ⟨true, false, true, false, false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f21 ⟨true, false, true, false, false, false, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, false, true, false, false, false, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b7
                        · cases b8
                          · exact (f58 ⟨true, false, true, false, false, false, false, false, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g58 ⟨true, false, true, false, false, false, false, false, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f71 ⟨true, false, true, false, false, false, false, false, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g71 ⟨true, false, true, false, false, false, false, false, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · exact (f78 ⟨true, false, true, false, false, false, false, true, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g78 ⟨true, false, true, false, false, false, false, true, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f101 ⟨true, false, true, false, false, false, false, true, b8, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g101 ⟨true, false, true, false, false, false, false, true, b8, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f44 ⟨true, false, true, false, false, false, false, b7, false, b9, false, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, false, false, false, false, b7, false, b9, false, b11, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, false, true, false, false, false, false, b7, true, b9, false, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, false, false, false, false, b7, true, b9, false, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b13
                      · cases b11
                        · cases b7
                          · cases b9
                            · exact (f87 ⟨true, false, true, false, false, false, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, false, false, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f95 ⟨true, false, true, false, false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g95 ⟨true, false, true, false, false, false, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b9
                            · exact (f87 ⟨true, false, true, false, false, false, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, false, false, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f78 ⟨true, false, true, false, false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g78 ⟨true, false, true, false, false, false, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b9
                          · exact (f61 ⟨true, false, true, false, false, false, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, true, false, false, false, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f95 ⟨true, false, true, false, false, false, false, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g95 ⟨true, false, true, false, false, false, false, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f101 ⟨true, false, true, false, false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g101 ⟨true, false, true, false, false, false, false, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨true, false, true, false, false, false, false, b7, false, b9, true, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, false, false, false, false, b7, false, b9, true, b11, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · cases b11
                        · cases b7
                          · cases b9
                            · exact (f87 ⟨true, false, true, false, false, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, false, false, false, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f95 ⟨true, false, true, false, false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g95 ⟨true, false, true, false, false, false, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b9
                            · exact (f87 ⟨true, false, true, false, false, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, false, false, false, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f78 ⟨true, false, true, false, false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g78 ⟨true, false, true, false, false, false, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b9
                          · exact (f61 ⟨true, false, true, false, false, false, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, true, false, false, false, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f95 ⟨true, false, true, false, false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g95 ⟨true, false, true, false, false, false, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f101 ⟨true, false, true, false, false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g101 ⟨true, false, true, false, false, false, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, false, true, false, false, false, false, b7, true, b9, true, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, false, false, false, false, b7, true, b9, true, b11, false, true⟩ rfl rfl rfl rfl).symm
                · cases b11
                  · cases b10
                    · cases b9
                      · cases b7
                        · cases b8
                          · cases b13
                            · exact (f77 ⟨true, false, true, true, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, false, true, true, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, true, true, false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, true, false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f60 ⟨true, false, true, true, false, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, false, true, true, false, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f39 ⟨true, false, true, true, false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, true, false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b8
                          · cases b13
                            · exact (f6 ⟨true, false, true, true, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, true, true, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, false, true, true, false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, true, false, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f2 ⟨true, false, true, true, false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g2 ⟨true, false, true, true, false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f39 ⟨true, false, true, true, false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, true, false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b13
                        · exact (f12 ⟨true, false, true, true, false, false, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, true, false, false, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b8
                          · exact (f44 ⟨true, false, true, true, false, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, true, false, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                          · exact (f39 ⟨true, false, true, true, false, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, true, false, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b9
                      · cases b8
                        · cases b13
                          · exact (f75 ⟨true, false, true, true, false, false, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, false, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f44 ⟨true, false, true, true, false, false, false, b7, false, false, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, true, false, false, false, b7, false, false, true, false, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b13
                          · exact (f75 ⟨true, false, true, true, false, false, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, false, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f39 ⟨true, false, true, true, false, false, false, b7, true, false, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, true, false, false, false, b7, true, false, true, false, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b13
                        · exact (f12 ⟨true, false, true, true, false, false, false, b7, b8, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, true, false, false, false, b7, b8, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b8
                          · exact (f44 ⟨true, false, true, true, false, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, true, false, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                          · exact (f39 ⟨true, false, true, true, false, false, false, b7, true, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, true, false, false, false, b7, true, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b9
                    · cases b8
                      · cases b13
                        · cases b10
                          · exact (f74 ⟨true, false, true, true, false, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, true, true, false, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, true, true, false, false, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, false, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f44 ⟨true, false, true, true, false, false, false, b7, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, true, false, false, false, b7, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b13
                        · cases b10
                          · exact (f74 ⟨true, false, true, true, false, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, true, true, false, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, true, true, false, false, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, false, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f39 ⟨true, false, true, true, false, false, false, b7, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, true, false, false, false, b7, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f12 ⟨true, false, true, true, false, false, false, b7, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, true, false, false, false, b7, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b8
                        · exact (f44 ⟨true, false, true, true, false, false, false, b7, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, true, true, false, false, false, b7, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f39 ⟨true, false, true, true, false, false, false, b7, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, true, true, false, false, false, b7, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
              · cases b11
                · cases b10
                  · cases b9
                    · cases b7
                      · cases b13
                        · cases b8
                          · cases b3
                            · exact (f63 ⟨true, false, true, false, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g63 ⟨true, false, true, false, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f77 ⟨true, false, true, true, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, false, true, true, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f60 ⟨true, false, true, b3, false, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, false, true, b3, false, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, true, b3, false, true, false, false, b8, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, b3, false, true, false, false, b8, false, false, false, false, true⟩ rfl rfl).symm
                      · cases b8
                        · cases b3
                          · cases b13
                            · exact (f81 ⟨true, false, true, false, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g81 ⟨true, false, true, false, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, true, false, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, false, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).symm
                          · cases b13
                            · exact (f6 ⟨true, false, true, true, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, true, true, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, true, true, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, true, false, true, false, true, false, false, false, false, false, true⟩ rfl rfl).symm
                        · cases b13
                          · exact (f2 ⟨true, false, true, b3, false, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g2 ⟨true, false, true, b3, false, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, true, b3, false, true, false, true, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, b3, false, true, false, true, true, false, false, false, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b8
                        · cases b7
                          · exact (f64 ⟨true, false, true, b3, false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, false, true, b3, false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f90 ⟨true, false, true, false, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g90 ⟨true, false, true, false, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f99 ⟨true, false, true, true, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g99 ⟨true, false, true, true, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · exact (f98 ⟨true, false, true, false, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, false, true, false, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f50 ⟨true, false, true, true, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, false, true, true, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, true, b3, false, true, false, b7, b8, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, b3, false, true, false, b7, b8, true, false, false, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b8
                      · cases b7
                        · cases b9
                          · cases b3
                            · exact (f87 ⟨true, false, true, false, false, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, false, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, true, true, false, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f64 ⟨true, false, true, b3, false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, false, true, b3, false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b9
                          · cases b3
                            · exact (f87 ⟨true, false, true, false, false, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, false, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, true, true, false, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f90 ⟨true, false, true, false, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g90 ⟨true, false, true, false, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f99 ⟨true, false, true, true, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g99 ⟨true, false, true, true, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b9
                        · cases b3
                          · exact (f87 ⟨true, false, true, false, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, true, true, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b7
                          · exact (f119 ⟨true, false, true, b3, false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g119 ⟨true, false, true, b3, false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f79 ⟨true, false, true, false, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g79 ⟨true, false, true, false, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f104 ⟨true, false, true, true, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g104 ⟨true, false, true, true, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, true, b3, false, true, false, b7, b8, b9, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, b3, false, true, false, b7, b8, b9, true, false, false, true⟩ rfl rfl).symm
                · cases b9
                  · cases b10
                    · cases b13
                      · cases b3
                        · exact (f19 ⟨true, false, true, false, false, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, false, false, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f94 ⟨true, false, true, true, false, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, false, true, true, false, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, true, b3, false, true, false, b7, b8, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, b3, false, true, false, b7, b8, false, false, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b3
                        · exact (f61 ⟨true, false, true, false, false, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, true, false, false, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, false, true, true, false, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, false, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, true, b3, false, true, false, b7, b8, false, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, b3, false, true, false, b7, b8, false, true, true, false, true⟩ rfl rfl).symm
                  · cases b3
                    · cases b10
                      · cases b8
                        · cases b13
                          · exact (f100 ⟨true, false, true, false, false, true, false, b7, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g100 ⟨true, false, true, false, false, true, false, b7, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, true, false, false, true, false, b7, false, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, false, false, true, false, b7, false, true, false, true, false, true⟩ rfl rfl).symm
                        · cases b7
                          · cases b13
                            · exact (f14 ⟨true, false, true, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, true, false, false, true, false, false, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, false, false, true, false, false, true, true, false, true, false, true⟩ rfl rfl).symm
                          · cases b13
                            · exact (f108 ⟨true, false, true, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f59 ⟨true, false, true, false, false, true, false, true, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, false, false, true, false, true, true, true, false, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · cases b8
                          · exact (f100 ⟨true, false, true, false, false, true, false, b7, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g100 ⟨true, false, true, false, false, true, false, b7, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f26 ⟨true, false, true, false, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, false, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, false, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, false, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, true, false, false, true, false, b7, b8, true, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, false, false, true, false, b7, b8, true, true, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b8
                        · exact (f17 ⟨true, false, true, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · cases b7
                            · exact (f9 ⟨true, false, true, true, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g9 ⟨true, false, true, true, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f108 ⟨true, false, true, true, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, true, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f26 ⟨true, false, true, true, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, true, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, true, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, true, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, true, true, false, true, false, b7, b8, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, true, true, false, true, false, b7, b8, true, b10, true, false, true⟩ rfl rfl).symm
          · cases b9
            · cases b13
              · cases b5
                · cases b10
                  · cases b8
                    · cases b11
                      · cases b7
                        · cases b3
                          · exact (f47 ⟨true, false, b2, false, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, false, b2, false, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f77 ⟨true, false, b2, true, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, false, b2, true, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · exact (f47 ⟨true, false, b2, false, true, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, false, b2, false, true, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f6 ⟨true, false, b2, true, true, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, b2, true, true, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f8 ⟨true, false, b2, false, true, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, b2, false, true, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f74 ⟨true, false, b2, true, true, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, b2, true, true, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b11
                      · exact (f3 ⟨true, false, b2, b3, true, false, false, b7, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g3 ⟨true, false, b2, b3, true, false, false, b7, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f8 ⟨true, false, b2, false, true, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, false, b2, false, true, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f74 ⟨true, false, b2, true, true, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, b2, true, true, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · cases b3
                      · exact (f87 ⟨true, false, b2, false, true, false, false, b7, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, b2, false, true, false, false, b7, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, false, b2, true, true, false, false, b7, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, true, false, false, b7, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f61 ⟨true, false, b2, false, true, false, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, b2, false, true, false, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, false, b2, true, true, false, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, true, false, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b11
                  · cases b8
                    · cases b7
                      · cases b3
                        · cases b10
                          · exact (f63 ⟨true, false, b2, false, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g63 ⟨true, false, b2, false, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f87 ⟨true, false, b2, false, true, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, b2, false, true, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f77 ⟨true, false, b2, true, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, false, b2, true, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, b2, true, true, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, true, true, false, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b10
                          · exact (f81 ⟨true, false, b2, false, true, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g81 ⟨true, false, b2, false, true, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f87 ⟨true, false, b2, false, true, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, b2, false, true, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f6 ⟨true, false, b2, true, true, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, false, b2, true, true, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, b2, true, true, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, true, true, false, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · exact (f70 ⟨true, false, b2, b3, true, true, false, b7, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g70 ⟨true, false, b2, b3, true, true, false, b7, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f87 ⟨true, false, b2, false, true, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, b2, false, true, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, false, b2, true, true, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, true, true, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b10
                    · cases b3
                      · cases b7
                        · cases b2
                          · exact (f37 ⟨true, false, false, false, true, true, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g37 ⟨true, false, false, false, true, true, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f19 ⟨true, false, true, false, true, true, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, false, true, true, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f13 ⟨true, false, false, false, true, true, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g13 ⟨true, false, false, false, true, true, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f19 ⟨true, false, true, false, true, true, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, false, true, true, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f52 ⟨true, false, b2, true, true, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, false, b2, true, true, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f61 ⟨true, false, b2, false, true, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, b2, false, true, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, false, b2, true, true, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, true, true, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
              · cases b8
                · cases b5
                  · exact (f44 ⟨true, false, b2, b3, true, false, false, b7, false, false, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, b2, b3, true, false, false, b7, false, false, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, false, b2, b3, true, true, false, b7, false, false, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, true, true, false, b7, false, false, b10, b11, false, true⟩ rfl rfl).symm
                · cases b5
                  · exact (f39 ⟨true, false, b2, b3, true, false, false, b7, true, false, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, b2, b3, true, false, false, b7, true, false, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, false, b2, b3, true, true, false, b7, true, false, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, true, true, false, b7, true, false, b10, b11, false, true⟩ rfl rfl).symm
            · cases b5
              · cases b13
                · exact (f5 ⟨true, false, b2, b3, true, false, false, b7, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g5 ⟨true, false, b2, b3, true, false, false, b7, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                · cases b8
                  · exact (f44 ⟨true, false, b2, b3, true, false, false, b7, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, b2, b3, true, false, false, b7, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f39 ⟨true, false, b2, b3, true, false, false, b7, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, b2, b3, true, false, false, b7, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
              · cases b8
                · cases b13
                  · exact (f7 ⟨true, false, b2, b3, true, true, false, b7, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, false, b2, b3, true, true, false, b7, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, false, b2, b3, true, true, false, b7, false, true, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, true, true, false, b7, false, true, b10, b11, false, true⟩ rfl rfl).symm
                · cases b3
                  · cases b11
                    · cases b13
                      · cases b7
                        · cases b2
                          · exact (f115 ⟨true, false, false, false, true, true, false, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, false, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f98 ⟨true, false, true, false, true, true, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, false, true, false, true, true, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f34 ⟨true, false, true, false, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g34 ⟨true, false, true, false, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f98 ⟨true, false, true, false, true, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, false, true, false, true, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f28 ⟨true, false, true, false, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g28 ⟨true, false, true, false, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, false, true, true, false, b7, true, true, b10, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, true, true, false, b7, true, true, b10, false, false, true⟩ rfl rfl).symm
                    · cases b10
                      · cases b7
                        · cases b13
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f14 ⟨true, false, true, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, false, true, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, b2, false, true, true, false, false, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, true, true, false, false, true, true, false, true, false, true⟩ rfl rfl).symm
                        · cases b13
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f108 ⟨true, false, true, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, false, b2, false, true, true, false, true, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, true, true, false, true, true, true, false, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · cases b7
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f72 ⟨true, false, true, false, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g72 ⟨true, false, true, false, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, false, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, false, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, b2, false, true, true, false, b7, true, true, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, true, true, false, b7, true, true, true, true, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b2
                      · exact (f115 ⟨true, false, false, true, true, true, false, b7, true, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, true, true, false, b7, true, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · cases b11
                          · exact (f50 ⟨true, false, true, true, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, false, true, true, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f9 ⟨true, false, true, true, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g9 ⟨true, false, true, true, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f108 ⟨true, false, true, true, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, true, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · cases b7
                            · exact (f34 ⟨true, false, true, true, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g34 ⟨true, false, true, true, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f28 ⟨true, false, true, true, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g28 ⟨true, false, true, true, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f72 ⟨true, false, true, true, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g72 ⟨true, false, true, true, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, true, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, true, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, b2, true, true, true, false, b7, true, true, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, true, true, true, false, b7, true, true, b10, b11, false, true⟩ rfl rfl).symm
      · cases b11
        · cases b10
          · cases b9
            · cases b0
              · cases b2
                · cases b8
                  · cases b13
                    · cases b7
                      · cases b4
                        · exact (f56 ⟨false, true, false, b3, false, b5, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b5
                          · exact (f91 ⟨false, true, false, b3, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f54 ⟨false, true, false, b3, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f44 ⟨false, true, false, b3, b4, false, false, b7, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, false, b3, b4, false, false, b7, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, false, false, false, false, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b7
                      · cases b4
                        · exact (f56 ⟨false, true, false, b3, false, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b5
                          · exact (f91 ⟨false, true, false, b3, false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f54 ⟨false, true, false, b3, false, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨false, true, false, b3, b4, false, false, b7, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, false, b3, b4, false, false, b7, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, true, false, false, false, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b5
                    · exact (f42 ⟨false, true, true, b3, b4, false, false, b7, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, false, b7, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f29 ⟨false, true, true, b3, b4, true, false, b7, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, b7, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b5
                      · exact (f44 ⟨false, true, true, b3, b4, false, false, b7, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, true, b3, b4, false, false, b7, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, false, false, false, false, false, true⟩ rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨false, true, true, b3, b4, false, false, b7, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, true, b3, b4, false, false, b7, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, true, false, false, false, false, true⟩ rfl rfl).symm
              · cases b7
                · cases b4
                  · cases b8
                    · cases b13
                      · cases b5
                        · cases b3
                          · exact (f47 ⟨true, true, b2, false, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, true, b2, false, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f77 ⟨true, true, b2, true, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, true, b2, true, false, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · exact (f63 ⟨true, true, b2, false, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g63 ⟨true, true, b2, false, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f77 ⟨true, true, b2, true, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, true, b2, true, false, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f44 ⟨true, true, b2, b3, false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, b3, false, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, false, true, false, false, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, false, false, false, false, false, false, false, true⟩ rfl rfl).symm
                    · cases b13
                      · exact (f60 ⟨true, true, b2, b3, false, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, true, b2, b3, false, b5, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, true, b2, b3, false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, b3, false, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, false, true, false, false, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, false, false, true, false, false, false, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b5
                      · cases b8
                        · cases b3
                          · exact (f47 ⟨true, true, b2, false, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, true, b2, false, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f77 ⟨true, true, b2, true, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, true, b2, true, true, false, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f3 ⟨true, true, b2, b3, true, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, b2, b3, true, false, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b8
                          · exact (f63 ⟨true, true, b2, false, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g63 ⟨true, true, b2, false, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f70 ⟨true, true, b2, false, true, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g70 ⟨true, true, b2, false, true, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b8
                          · exact (f77 ⟨true, true, b2, true, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, true, b2, true, true, true, false, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f70 ⟨true, true, b2, true, true, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g70 ⟨true, true, b2, true, true, true, false, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · cases b5
                        · exact (f44 ⟨true, true, b2, b3, true, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, b3, true, false, false, false, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, true, true, false, false, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, false, false, false, false, false, false, true⟩ rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, true, b2, b3, true, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, b3, true, false, false, false, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, true, true, false, false, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, false, true, false, false, false, false, true⟩ rfl rfl).symm
                · cases b8
                  · cases b3
                    · cases b13
                      · cases b5
                        · exact (f47 ⟨true, true, b2, false, b4, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, true, b2, false, b4, false, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f81 ⟨true, true, b2, false, b4, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g81 ⟨true, true, b2, false, b4, true, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f44 ⟨true, true, b2, false, b4, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, false, b4, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, b4, true, false, true, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, b4, true, false, true, false, false, false, false, false, true⟩ rfl rfl).symm
                    · cases b13
                      · exact (f6 ⟨true, true, b2, true, b4, b5, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, true, b2, true, b4, b5, false, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f44 ⟨true, true, b2, true, b4, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, true, b4, false, false, true, false, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, true, b4, true, false, true, false, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, b4, true, false, true, false, false, false, false, false, true⟩ rfl rfl).symm
                  · cases b4
                    · cases b13
                      · exact (f2 ⟨true, true, b2, b3, false, b5, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g2 ⟨true, true, b2, b3, false, b5, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, true, b2, b3, false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, b3, false, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, false, true, false, true, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, false, true, true, false, false, false, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b5
                        · exact (f3 ⟨true, true, b2, b3, true, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g3 ⟨true, true, b2, b3, true, false, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f70 ⟨true, true, b2, b3, true, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g70 ⟨true, true, b2, b3, true, true, false, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, true, b2, b3, true, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, b3, true, false, false, true, true, false, false, false, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, true, true, false, true, true, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, true, true, false, false, false, false, true⟩ rfl rfl).symm
            · cases b0
              · cases b2
                · cases b8
                  · cases b13
                    · cases b7
                      · cases b4
                        · exact (f56 ⟨false, true, false, b3, false, b5, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b5
                          · exact (f91 ⟨false, true, false, b3, false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f54 ⟨false, true, false, b3, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f44 ⟨false, true, false, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, false, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b7
                      · cases b4
                        · exact (f56 ⟨false, true, false, b3, false, b5, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b5
                          · exact (f91 ⟨false, true, false, b3, false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f54 ⟨false, true, false, b3, false, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, true, false, b3, true, b5, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨false, true, false, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, false, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b5
                    · exact (f42 ⟨false, true, true, b3, b4, false, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f29 ⟨false, true, true, b3, b4, true, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b5
                      · exact (f44 ⟨false, true, true, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, true, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨false, true, true, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, true, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).symm
              · cases b5
                · cases b2
                  · cases b8
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, false, b7, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, false, b7, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨true, true, false, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, false, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, false, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, false, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f10 ⟨true, true, true, b3, b4, false, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, true, true, b3, b4, false, false, b7, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f44 ⟨true, true, true, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, true, b3, b4, false, false, b7, false, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, true, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, true, b3, b4, false, false, b7, true, true, false, false, false, true⟩ rfl rfl rfl rfl).symm
                · cases b4
                  · cases b13
                    · cases b8
                      · cases b7
                        · exact (f64 ⟨true, true, b2, b3, false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, true, b2, b3, false, true, false, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f111 ⟨true, true, b2, b3, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g111 ⟨true, true, b2, b3, false, true, false, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b2
                          · exact (f115 ⟨true, true, false, false, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f98 ⟨true, true, true, false, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, true, true, false, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, true, false, true, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f50 ⟨true, true, true, true, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, true, true, true, false, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, false, true, false, b7, b8, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, false, b7, b8, true, false, false, false, true⟩ rfl rfl).symm
                  · cases b8
                    · cases b13
                      · exact (f7 ⟨true, true, b2, b3, true, true, false, b7, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, true, b2, b3, true, true, false, b7, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, true, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, b7, false, true, false, false, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b3
                        · cases b2
                          · exact (f115 ⟨true, true, false, false, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f98 ⟨true, true, true, false, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, true, true, false, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, true, false, true, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f50 ⟨true, true, true, true, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, true, true, true, true, true, false, b7, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, true, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, b7, true, true, false, false, false, true⟩ rfl rfl).symm
          · cases b0
            · cases b2
              · cases b8
                · cases b13
                  · cases b7
                    · cases b4
                      · exact (f56 ⟨false, true, false, b3, false, b5, false, false, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, b5, false, false, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, false, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · cases b5
                        · exact (f91 ⟨false, true, false, b3, false, false, false, true, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f54 ⟨false, true, false, b3, false, true, false, true, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, b5, false, true, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, true, false, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · exact (f44 ⟨false, true, false, b3, b4, false, false, b7, false, b9, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, false, b3, b4, false, false, b7, false, b9, true, false, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, false, b9, true, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, false, b9, true, false, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b7
                    · cases b4
                      · exact (f56 ⟨false, true, false, b3, false, b5, false, false, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, b5, false, false, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, false, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · cases b5
                        · exact (f91 ⟨false, true, false, b3, false, false, false, true, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f54 ⟨false, true, false, b3, false, true, false, true, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, b5, false, true, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, b5, false, true, true, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · exact (f39 ⟨false, true, false, b3, b4, false, false, b7, true, b9, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, false, b3, b4, false, false, b7, true, b9, true, false, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, true, b9, true, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, true, b9, true, false, false, true⟩ rfl rfl).symm
              · cases b13
                · cases b5
                  · exact (f42 ⟨false, true, true, b3, b4, false, false, b7, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, false, b7, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f29 ⟨false, true, true, b3, b4, true, false, b7, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, b7, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b8
                  · cases b5
                    · exact (f44 ⟨false, true, true, b3, b4, false, false, b7, false, b9, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, true, b3, b4, false, false, b7, false, b9, true, false, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, false, b9, true, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, false, b9, true, false, false, true⟩ rfl rfl).symm
                  · cases b5
                    · exact (f39 ⟨false, true, true, b3, b4, false, false, b7, true, b9, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, true, b3, b4, false, false, b7, true, b9, true, false, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, true, b9, true, false, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, true, b9, true, false, false, true⟩ rfl rfl).symm
            · cases b9
              · cases b8
                · cases b13
                  · cases b3
                    · exact (f87 ⟨true, true, b2, false, b4, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, true, b2, false, b4, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f75 ⟨true, true, b2, true, b4, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, false, b7, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · exact (f44 ⟨true, true, b2, b3, b4, false, false, b7, false, false, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, b3, b4, false, false, b7, false, false, true, false, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, b4, true, false, b7, false, false, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, b4, true, false, b7, false, false, true, false, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b3
                    · exact (f87 ⟨true, true, b2, false, b4, b5, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, true, b2, false, b4, b5, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f75 ⟨true, true, b2, true, b4, b5, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, false, b7, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · exact (f39 ⟨true, true, b2, b3, b4, false, false, b7, true, false, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, b3, b4, false, false, b7, true, false, true, false, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, b4, true, false, b7, true, false, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, b4, true, false, b7, true, false, true, false, false, true⟩ rfl rfl).symm
              · cases b5
                · cases b2
                  · cases b8
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, false, b7, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, false, b7, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨true, true, false, b3, b4, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, false, b3, b4, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, false, b7, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, false, b7, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, false, b3, b4, false, false, b7, true, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, false, b3, b4, false, false, b7, true, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f10 ⟨true, true, true, b3, b4, false, false, b7, b8, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, true, true, b3, b4, false, false, b7, b8, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f44 ⟨true, true, true, b3, b4, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, true, b3, b4, false, false, b7, false, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, true, b3, b4, false, false, b7, true, true, true, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, true, b3, b4, false, false, b7, true, true, true, false, false, true⟩ rfl rfl rfl rfl).symm
                · cases b4
                  · cases b13
                    · cases b8
                      · cases b7
                        · exact (f64 ⟨true, true, b2, b3, false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, true, b2, b3, false, true, false, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f111 ⟨true, true, b2, b3, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g111 ⟨true, true, b2, b3, false, true, false, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b7
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f119 ⟨true, true, true, b3, false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g119 ⟨true, true, true, b3, false, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f79 ⟨true, true, true, false, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g79 ⟨true, true, true, false, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, true, false, true, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f104 ⟨true, true, true, true, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g104 ⟨true, true, true, true, false, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, false, true, false, b7, b8, true, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, false, b7, b8, true, true, false, false, true⟩ rfl rfl).symm
                  · cases b8
                    · cases b13
                      · exact (f7 ⟨true, true, b2, b3, true, true, false, b7, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, true, b2, b3, true, true, false, b7, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, true, true, false, b7, false, true, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, b7, false, true, true, false, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b7
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f34 ⟨true, true, true, b3, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g34 ⟨true, true, true, b3, true, true, false, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f28 ⟨true, true, true, b3, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g28 ⟨true, true, true, b3, true, true, false, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, true, true, false, b7, true, true, true, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, b7, true, true, true, false, false, true⟩ rfl rfl).symm
        · cases b0
          · cases b2
            · cases b8
              · cases b13
                · cases b7
                  · cases b4
                    · exact (f56 ⟨false, true, false, b3, false, b5, false, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, true, false, b3, true, b5, false, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, b5, false, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b4
                    · cases b5
                      · exact (f91 ⟨false, true, false, b3, false, false, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f54 ⟨false, true, false, b3, false, true, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, true, false, b3, true, b5, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, b5, false, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b5
                  · exact (f44 ⟨false, true, false, b3, b4, false, false, b7, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, false, b3, b4, false, false, b7, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, false, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, false, b9, b10, true, false, true⟩ rfl rfl).symm
              · cases b13
                · cases b7
                  · cases b4
                    · exact (f56 ⟨false, true, false, b3, false, b5, false, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, b5, false, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, true, false, b3, true, b5, false, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, b5, false, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b4
                    · cases b5
                      · exact (f91 ⟨false, true, false, b3, false, false, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f54 ⟨false, true, false, b3, false, true, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, true, false, b3, true, b5, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, b5, false, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b5
                  · exact (f39 ⟨false, true, false, b3, b4, false, false, b7, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, false, b3, b4, false, false, b7, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, true, false, b3, b4, true, false, b7, true, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, false, b7, true, b9, b10, true, false, true⟩ rfl rfl).symm
            · cases b13
              · cases b5
                · exact (f42 ⟨false, true, true, b3, b4, false, false, b7, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, false, b7, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f29 ⟨false, true, true, b3, b4, true, false, b7, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, b7, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
              · cases b8
                · cases b5
                  · exact (f44 ⟨false, true, true, b3, b4, false, false, b7, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, true, b3, b4, false, false, b7, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, false, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, false, b9, b10, true, false, true⟩ rfl rfl).symm
                · cases b5
                  · exact (f39 ⟨false, true, true, b3, b4, false, false, b7, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, true, b3, b4, false, false, b7, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, true, true, b3, b4, true, false, b7, true, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, false, b7, true, b9, b10, true, false, true⟩ rfl rfl).symm
          · cases b9
            · cases b3
              · cases b4
                · cases b10
                  · cases b5
                    · cases b7
                      · cases b2
                        · cases b8
                          · cases b13
                            · exact (f83 ⟨true, true, false, false, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g83 ⟨true, true, false, false, false, false, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f44 ⟨true, true, false, false, false, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, false, false, false, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                          · cases b13
                            · exact (f83 ⟨true, true, false, false, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g83 ⟨true, true, false, false, false, false, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f39 ⟨true, true, false, false, false, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, false, false, false, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                        · cases b13
                          · exact (f27 ⟨true, true, true, false, false, false, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g27 ⟨true, true, true, false, false, false, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b8
                            · exact (f44 ⟨true, true, true, false, false, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, true, false, false, false, false, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                            · exact (f39 ⟨true, true, true, false, false, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, true, false, false, false, false, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                      · cases b13
                        · exact (f21 ⟨true, true, b2, false, false, false, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g21 ⟨true, true, b2, false, false, false, false, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b8
                          · exact (f44 ⟨true, true, b2, false, false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, false, false, false, false, true, false, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                          · exact (f39 ⟨true, true, b2, false, false, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, false, false, false, false, true, true, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · cases b2
                        · cases b7
                          · exact (f46 ⟨true, true, false, false, false, true, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g46 ⟨true, true, false, false, false, true, false, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b8
                            · exact (f33 ⟨true, true, false, false, false, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g33 ⟨true, true, false, false, false, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f62 ⟨true, true, false, false, false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g62 ⟨true, true, false, false, false, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f19 ⟨true, true, true, false, false, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, true, true, false, false, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, false, false, true, false, b7, b8, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, b7, b8, false, false, true, false, true⟩ rfl rfl).symm
                  · cases b8
                    · cases b13
                      · exact (f61 ⟨true, true, b2, false, false, b5, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, true, b2, false, false, b5, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f44 ⟨true, true, b2, false, false, false, false, b7, false, false, true, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, false, false, false, false, b7, false, false, true, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, false, true, false, b7, false, false, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, b7, false, false, true, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · exact (f61 ⟨true, true, b2, false, false, b5, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, true, b2, false, false, b5, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, true, b2, false, false, false, false, b7, true, false, true, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, false, false, false, false, b7, true, false, true, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, false, true, false, b7, true, false, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, b7, true, false, true, true, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b10
                    · cases b5
                      · exact (f8 ⟨true, true, b2, false, true, false, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, true, b2, false, true, false, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · cases b8
                          · cases b7
                            · exact (f37 ⟨true, true, false, false, true, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g37 ⟨true, true, false, false, true, true, false, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f96 ⟨true, true, false, false, true, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g96 ⟨true, true, false, false, true, true, false, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f37 ⟨true, true, false, false, true, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g37 ⟨true, true, false, false, true, true, false, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f35 ⟨true, true, false, false, true, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g35 ⟨true, true, false, false, true, true, false, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f19 ⟨true, true, true, false, true, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, true, true, false, true, true, false, b7, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f61 ⟨true, true, b2, false, true, b5, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, true, b2, false, true, b5, false, b7, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b5
                      · exact (f44 ⟨true, true, b2, false, true, false, false, b7, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, false, true, false, false, b7, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, false, true, true, false, b7, false, false, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, true, true, false, b7, false, false, b10, true, false, true⟩ rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨true, true, b2, false, true, false, false, b7, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, false, true, false, false, b7, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, false, true, true, false, b7, true, false, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, true, true, false, b7, true, false, b10, true, false, true⟩ rfl rfl).symm
              · cases b8
                · cases b13
                  · cases b10
                    · cases b4
                      · cases b5
                        · exact (f74 ⟨true, true, b2, true, false, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, false, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f94 ⟨true, true, b2, true, false, true, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, true, b2, true, false, true, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f74 ⟨true, true, b2, true, true, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, true, false, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f52 ⟨true, true, b2, true, true, true, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, true, b2, true, true, true, false, b7, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f75 ⟨true, true, b2, true, b4, b5, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, false, b7, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · exact (f44 ⟨true, true, b2, true, b4, false, false, b7, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, true, b4, false, false, b7, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, true, b4, true, false, b7, false, false, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, b4, true, false, b7, false, false, b10, true, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b10
                    · cases b4
                      · cases b5
                        · exact (f74 ⟨true, true, b2, true, false, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, false, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f94 ⟨true, true, b2, true, false, true, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, true, b2, true, false, true, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f74 ⟨true, true, b2, true, true, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, true, false, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f52 ⟨true, true, b2, true, true, true, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, true, b2, true, true, true, false, b7, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f75 ⟨true, true, b2, true, b4, b5, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, false, b7, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · exact (f39 ⟨true, true, b2, true, b4, false, false, b7, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, true, b4, false, false, b7, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, true, b4, true, false, b7, true, false, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, b4, true, false, b7, true, false, b10, true, false, true⟩ rfl rfl).symm
            · cases b5
              · cases b2
                · cases b8
                  · cases b13
                    · exact (f55 ⟨true, true, false, b3, b4, false, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨true, true, false, b3, b4, false, false, b7, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, false, b3, b4, false, false, b7, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f55 ⟨true, true, false, b3, b4, false, false, b7, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, false, b7, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f39 ⟨true, true, false, b3, b4, false, false, b7, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, false, b3, b4, false, false, b7, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f10 ⟨true, true, true, b3, b4, false, false, b7, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, true, true, b3, b4, false, false, b7, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · exact (f44 ⟨true, true, true, b3, b4, false, false, b7, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, true, b3, b4, false, false, b7, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f39 ⟨true, true, true, b3, b4, false, false, b7, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, true, b3, b4, false, false, b7, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
              · cases b4
                · cases b3
                  · cases b10
                    · cases b8
                      · cases b13
                        · exact (f40 ⟨true, true, b2, false, false, true, false, b7, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, b2, false, false, true, false, b7, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, false, true, false, b7, false, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, b7, false, true, false, true, false, true⟩ rfl rfl).symm
                      · cases b7
                        · cases b13
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f14 ⟨true, true, true, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, true, true, false, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, true, b2, false, false, true, false, false, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, false, true, true, false, true, false, true⟩ rfl rfl).symm
                        · cases b13
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f118 ⟨true, true, true, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g118 ⟨true, true, true, false, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, true, b2, false, false, true, false, true, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, true, true, true, false, true, false, true⟩ rfl rfl).symm
                    · cases b8
                      · cases b13
                        · exact (f40 ⟨true, true, b2, false, false, true, false, b7, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, b2, false, false, true, false, b7, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, false, true, false, b7, false, true, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, b7, false, true, true, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · cases b2
                          · exact (f115 ⟨true, true, false, false, false, true, false, b7, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, false, true, false, b7, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f114 ⟨true, true, true, false, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g114 ⟨true, true, true, false, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, true, true, false, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, true, true, false, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, false, true, false, b7, true, true, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, false, b7, true, true, true, true, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b2
                      · cases b8
                        · exact (f45 ⟨true, true, false, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, false, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f115 ⟨true, true, false, true, false, true, false, b7, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, false, true, false, b7, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b8
                        · exact (f45 ⟨true, true, true, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, true, true, false, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · cases b7
                            · exact (f9 ⟨true, true, true, true, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g9 ⟨true, true, true, true, false, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f118 ⟨true, true, true, true, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g118 ⟨true, true, true, true, false, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f114 ⟨true, true, true, true, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g114 ⟨true, true, true, true, false, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, true, true, true, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, true, true, true, false, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, true, false, true, false, b7, b8, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, false, true, false, b7, b8, true, b10, true, false, true⟩ rfl rfl).symm
                · cases b8
                  · cases b13
                    · exact (f7 ⟨true, true, b2, b3, true, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, true, b2, b3, true, true, false, b7, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, true, true, false, b7, false, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, false, b7, false, true, b10, true, false, true⟩ rfl rfl).symm
                  · cases b3
                    · cases b10
                      · cases b7
                        · cases b13
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f14 ⟨true, true, true, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, true, true, false, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, true, b2, false, true, true, false, false, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, true, true, false, false, true, true, false, true, false, true⟩ rfl rfl).symm
                        · cases b13
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f124 ⟨true, true, true, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g124 ⟨true, true, true, false, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f59 ⟨true, true, b2, false, true, true, false, true, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, true, true, false, true, true, true, false, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · cases b2
                          · exact (f115 ⟨true, true, false, false, true, true, false, b7, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, true, true, false, b7, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f86 ⟨true, true, true, false, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g86 ⟨true, true, true, false, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, true, true, false, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, true, true, false, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, true, true, false, b7, true, true, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, true, true, false, b7, true, true, true, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b2
                        · exact (f115 ⟨true, true, false, true, true, true, false, b7, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, true, true, false, b7, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · cases b7
                            · exact (f9 ⟨true, true, true, true, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g9 ⟨true, true, true, true, true, true, false, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f109 ⟨true, true, true, true, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g109 ⟨true, true, true, true, true, true, false, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b7
                            · exact (f86 ⟨true, true, true, true, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g86 ⟨true, true, true, true, true, true, false, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, true, true, true, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, true, true, true, true, true, false, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, true, true, true, false, b7, true, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, true, true, false, b7, true, true, b10, true, false, true⟩ rfl rfl).symm
    · cases b7
      · cases b11
        · cases b5
          · cases b1
            · cases b9
              · cases b8
                · cases b13
                  · cases b2
                    · cases b4
                      · cases b0
                        · exact (f56 ⟨false, false, false, b3, false, false, true, false, false, false, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, false, true, false, false, false, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f110 ⟨true, false, false, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, false, false, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f87 ⟨true, false, false, false, false, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, false, false, false, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, false, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · cases b0
                          · exact (f93 ⟨false, false, false, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f102 ⟨true, false, false, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, false, false, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · cases b0
                            · exact (f93 ⟨false, false, false, false, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, false, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f87 ⟨true, false, false, false, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, false, false, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b0
                            · exact (f93 ⟨false, false, false, true, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, true, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, true, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · cases b4
                        · cases b0
                          · exact (f126 ⟨false, false, true, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f110 ⟨true, false, true, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, false, true, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b0
                          · exact (f126 ⟨false, false, true, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f102 ⟨true, false, true, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, false, true, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b0
                          · exact (f85 ⟨false, false, true, false, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, false, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f87 ⟨true, false, true, false, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b0
                          · exact (f85 ⟨false, false, true, true, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, true, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, true, true, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f44 ⟨b0, false, b2, b3, b4, false, true, false, false, false, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨b0, false, b2, b3, b4, false, true, false, false, false, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b2
                    · cases b4
                      · cases b0
                        · exact (f56 ⟨false, false, false, b3, false, false, true, false, true, false, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, false, true, false, true, false, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f113 ⟨true, false, false, b3, false, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, false, b3, false, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b3
                            · exact (f87 ⟨true, false, false, false, false, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, false, false, false, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, false, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · cases b0
                          · exact (f93 ⟨false, false, false, b3, true, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f113 ⟨true, false, false, b3, true, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, false, b3, true, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · cases b0
                            · exact (f93 ⟨false, false, false, false, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, false, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f87 ⟨true, false, false, false, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, false, false, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b0
                            · exact (f93 ⟨false, false, false, true, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, true, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, true, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · cases b0
                        · exact (f126 ⟨false, false, true, b3, b4, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f113 ⟨true, false, true, b3, b4, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, true, b3, b4, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b0
                          · exact (f85 ⟨false, false, true, false, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, false, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f87 ⟨true, false, true, false, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, true, false, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b0
                          · exact (f85 ⟨false, false, true, true, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, true, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, true, true, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f39 ⟨b0, false, b2, b3, b4, false, true, false, true, false, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨b0, false, b2, b3, b4, false, true, false, true, false, b10, false, false, true⟩ rfl rfl rfl rfl).symm
              · cases b0
                · cases b8
                  · cases b13
                    · cases b2
                      · cases b4
                        · exact (f56 ⟨false, false, false, b3, false, false, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, false, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, false, false, b3, true, false, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · exact (f65 ⟨false, false, true, b3, b4, false, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f85 ⟨false, false, true, b3, b4, false, true, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨false, false, b2, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, false, b2, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b2
                      · cases b4
                        · exact (f56 ⟨false, false, false, b3, false, false, true, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, false, true, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f93 ⟨false, false, false, b3, true, false, true, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · exact (f65 ⟨false, false, true, b3, b4, false, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f85 ⟨false, false, true, b3, b4, false, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f39 ⟨false, false, b2, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, false, b2, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b4
                    · cases b2
                      · cases b3
                        · exact (f67 ⟨true, false, false, false, false, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f82 ⟨true, false, false, true, false, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b10
                          · cases b8
                            · exact (f58 ⟨true, false, true, false, false, false, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g58 ⟨true, false, true, false, false, false, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f71 ⟨true, false, true, false, false, false, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g71 ⟨true, false, true, false, false, false, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f95 ⟨true, false, true, false, false, false, true, false, b8, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g95 ⟨true, false, true, false, false, false, true, false, b8, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f12 ⟨true, false, true, true, false, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, true, false, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f5 ⟨true, false, b2, b3, true, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g5 ⟨true, false, b2, b3, true, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · exact (f44 ⟨true, false, b2, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, b2, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f39 ⟨true, false, b2, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, b2, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
            · cases b0
              · cases b8
                · cases b2
                  · cases b13
                    · cases b4
                      · exact (f56 ⟨false, true, false, b3, false, false, true, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, false, true, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, false, true, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, false, true, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨false, true, false, b3, b4, false, true, false, false, b9, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, false, b3, b4, false, true, false, false, b9, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f42 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b2
                    · cases b4
                      · exact (f56 ⟨false, true, false, b3, false, false, true, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, false, true, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, false, true, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, false, true, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f42 ⟨false, true, true, b3, b4, false, true, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, true, false, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f39 ⟨false, true, b2, b3, b4, false, true, false, true, b9, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, b2, b3, b4, false, true, false, true, b9, b10, false, false, true⟩ rfl rfl rfl rfl).symm
              · cases b9
                · cases b8
                  · cases b13
                    · cases b10
                      · cases b4
                        · exact (f110 ⟨true, true, b2, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, true, b2, b3, false, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f102 ⟨true, true, b2, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, true, b2, b3, true, false, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f87 ⟨true, true, b2, false, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, true, b2, false, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, true, b2, true, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, false, true, false, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨true, true, b2, b3, b4, false, true, false, false, false, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, b3, b4, false, true, false, false, false, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b10
                      · exact (f113 ⟨true, true, b2, b3, b4, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, true, b2, b3, b4, false, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f87 ⟨true, true, b2, false, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, true, b2, false, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, true, b2, true, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, false, true, false, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f39 ⟨true, true, b2, b3, b4, false, true, false, true, false, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, b3, b4, false, true, false, true, false, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                · cases b2
                  · cases b8
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f10 ⟨true, true, true, b3, b4, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, true, true, b3, b4, false, true, false, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f44 ⟨true, true, true, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, true, b3, b4, false, true, false, false, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, true, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, true, b3, b4, false, true, false, true, true, b10, false, false, true⟩ rfl rfl rfl rfl).symm
          · cases b13
            · cases b4
              · cases b0
                · cases b2
                  · exact (f56 ⟨false, b1, false, b3, false, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, b1, false, b3, false, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b1
                    · cases b10
                      · cases b9
                        · exact (f126 ⟨false, false, true, b3, false, true, true, false, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, false, true, true, false, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f65 ⟨false, false, true, b3, false, true, true, false, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, false, true, true, false, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, false, true, true, false, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, false, true, true, false, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f11 ⟨false, true, true, b3, false, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, false, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b9
                  · cases b10
                    · cases b8
                      · exact (f110 ⟨true, b1, b2, b3, false, true, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, b1, b2, b3, false, true, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f113 ⟨true, b1, b2, b3, false, true, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, b3, false, true, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f87 ⟨true, b1, b2, false, false, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, false, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, b1, b2, true, false, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, false, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b10
                    · cases b8
                      · exact (f64 ⟨true, b1, b2, b3, false, true, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, b1, b2, b3, false, true, true, false, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b2
                          · exact (f115 ⟨true, b1, false, false, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f98 ⟨true, b1, true, false, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, b1, true, false, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, b1, false, true, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, true, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f50 ⟨true, b1, true, true, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, b1, true, true, false, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f64 ⟨true, b1, b2, b3, false, true, true, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, b1, b2, b3, false, true, true, false, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, b1, false, b3, false, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, b3, false, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f1 ⟨true, b1, true, b3, false, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g1 ⟨true, b1, true, b3, false, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
              · cases b0
                · cases b2
                  · exact (f93 ⟨false, b1, false, b3, true, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, b1, false, b3, true, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b1
                    · cases b10
                      · cases b9
                        · exact (f126 ⟨false, false, true, b3, true, true, true, false, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, true, true, true, false, b8, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f65 ⟨false, false, true, b3, true, true, true, false, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, true, true, true, false, b8, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, true, true, true, false, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, true, true, true, false, b8, b9, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f11 ⟨false, true, true, b3, true, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, true, true, true, false, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b9
                  · cases b10
                    · cases b8
                      · exact (f102 ⟨true, b1, b2, b3, true, true, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, b1, b2, b3, true, true, true, false, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f113 ⟨true, b1, b2, b3, true, true, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, b3, true, true, true, false, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f87 ⟨true, b1, b2, false, true, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, true, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, b1, b2, true, true, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, true, true, true, false, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · exact (f7 ⟨true, b1, b2, b3, true, true, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, b1, b2, b3, true, true, true, false, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · cases b10
                        · cases b2
                          · exact (f115 ⟨true, b1, false, false, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f98 ⟨true, b1, true, false, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, b1, true, false, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, b1, false, false, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f51 ⟨true, b1, true, false, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, b1, true, false, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · cases b2
                          · exact (f115 ⟨true, b1, false, true, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, true, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f50 ⟨true, b1, true, true, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, b1, true, true, true, true, true, false, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, b1, false, true, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, true, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f51 ⟨true, b1, true, true, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, b1, true, true, true, true, true, false, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
            · exact (f59 ⟨b0, b1, b2, b3, b4, true, true, false, b8, b9, b10, false, false, true⟩ rfl rfl).trans (g59 ⟨b0, b1, b2, b3, b4, true, true, false, b8, b9, b10, false, false, true⟩ rfl rfl).symm
        · cases b1
          · cases b5
            · cases b9
              · cases b3
                · cases b10
                  · cases b13
                    · cases b0
                      · cases b2
                        · cases b4
                          · exact (f56 ⟨false, false, false, false, false, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, false, false, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f66 ⟨false, false, false, false, true, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, false, true, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f126 ⟨false, false, true, false, b4, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, false, b4, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f32 ⟨true, false, b2, false, b4, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g32 ⟨true, false, b2, false, b4, false, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f44 ⟨b0, false, b2, false, b4, false, true, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨b0, false, b2, false, b4, false, true, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f39 ⟨b0, false, b2, false, b4, false, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨b0, false, b2, false, b4, false, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b13
                      · cases b2
                        · cases b4
                          · cases b0
                            · exact (f56 ⟨false, false, false, false, false, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, false, false, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                            · exact (f61 ⟨true, false, false, false, false, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b0
                            · exact (f66 ⟨false, false, false, false, true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, false, true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                            · exact (f61 ⟨true, false, false, false, true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b0
                          · exact (f85 ⟨false, false, true, false, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, false, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f61 ⟨true, false, true, false, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, true, false, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨b0, false, b2, false, b4, false, true, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨b0, false, b2, false, b4, false, true, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · cases b2
                        · cases b4
                          · cases b0
                            · exact (f56 ⟨false, false, false, false, false, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, false, false, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                            · exact (f61 ⟨true, false, false, false, false, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, false, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b0
                            · exact (f66 ⟨false, false, false, false, true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, false, true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                            · exact (f61 ⟨true, false, false, false, true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, false, false, true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b0
                          · exact (f85 ⟨false, false, true, false, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, false, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f61 ⟨true, false, true, false, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, true, false, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f39 ⟨b0, false, b2, false, b4, false, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨b0, false, b2, false, b4, false, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl).symm
                · cases b8
                  · cases b13
                    · cases b2
                      · cases b4
                        · cases b0
                          · exact (f56 ⟨false, false, false, true, false, false, true, false, false, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, true, false, false, true, false, false, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f74 ⟨true, false, false, true, false, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, false, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, false, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b0
                          · exact (f66 ⟨false, false, false, true, true, false, true, false, false, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, true, true, false, true, false, false, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f74 ⟨true, false, false, true, true, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, true, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, true, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b0
                        · cases b10
                          · exact (f126 ⟨false, false, true, true, b4, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, true, b4, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f85 ⟨false, false, true, true, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, true, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f74 ⟨true, false, true, true, b4, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, true, true, b4, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, true, true, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, b4, false, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨b0, false, b2, true, b4, false, true, false, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨b0, false, b2, true, b4, false, true, false, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b2
                      · cases b4
                        · cases b0
                          · exact (f56 ⟨false, false, false, true, false, false, true, false, true, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, true, false, false, true, false, true, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f74 ⟨true, false, false, true, false, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, false, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, false, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, false, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b0
                          · exact (f66 ⟨false, false, false, true, true, false, true, false, true, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, true, true, false, true, false, true, false, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f74 ⟨true, false, false, true, true, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, true, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f75 ⟨true, false, false, true, true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, false, true, true, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b0
                        · cases b10
                          · exact (f126 ⟨false, false, true, true, b4, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, true, b4, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f85 ⟨false, false, true, true, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, true, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f74 ⟨true, false, true, true, b4, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, true, true, b4, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f75 ⟨true, false, true, true, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, true, true, b4, false, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f39 ⟨b0, false, b2, true, b4, false, true, false, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨b0, false, b2, true, b4, false, true, false, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
              · cases b0
                · cases b8
                  · cases b13
                    · cases b2
                      · cases b4
                        · exact (f56 ⟨false, false, false, b3, false, false, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, false, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f66 ⟨false, false, false, b3, true, false, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · exact (f65 ⟨false, false, true, b3, b4, false, true, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, true, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f85 ⟨false, false, true, b3, b4, false, true, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, false, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨false, false, b2, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, false, b2, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b2
                      · cases b4
                        · exact (f56 ⟨false, false, false, b3, false, false, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, false, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f66 ⟨false, false, false, b3, true, false, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · exact (f65 ⟨false, false, true, b3, b4, false, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f85 ⟨false, false, true, b3, b4, false, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f39 ⟨false, false, b2, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, false, b2, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b4
                    · cases b2
                      · cases b3
                        · exact (f67 ⟨true, false, false, false, false, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g67 ⟨true, false, false, false, false, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f82 ⟨true, false, false, true, false, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g82 ⟨true, false, false, true, false, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b10
                          · cases b8
                            · exact (f58 ⟨true, false, true, false, false, false, true, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g58 ⟨true, false, true, false, false, false, true, false, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f71 ⟨true, false, true, false, false, false, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g71 ⟨true, false, true, false, false, false, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f95 ⟨true, false, true, false, false, false, true, false, b8, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g95 ⟨true, false, true, false, false, false, true, false, b8, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f12 ⟨true, false, true, true, false, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, true, false, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f5 ⟨true, false, b2, b3, true, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g5 ⟨true, false, b2, b3, true, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · exact (f44 ⟨true, false, b2, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, b2, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f39 ⟨true, false, b2, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, b2, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
            · cases b0
              · cases b2
                · cases b4
                  · cases b13
                    · exact (f56 ⟨false, false, false, b3, false, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, false, false, b3, false, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, false, false, b3, false, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, false, false, b3, false, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).symm
                  · cases b13
                    · exact (f66 ⟨false, false, false, b3, true, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, false, false, b3, true, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, false, false, b3, true, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b10
                    · cases b9
                      · exact (f126 ⟨false, false, true, b3, b4, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f65 ⟨false, false, true, b3, b4, true, true, false, b8, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, true, true, false, b8, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f85 ⟨false, false, true, b3, b4, true, true, false, b8, b9, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, true, true, false, b8, b9, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, false, true, b3, b4, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).symm
              · cases b9
                · cases b3
                  · cases b10
                    · cases b13
                      · exact (f32 ⟨true, false, b2, false, b4, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g32 ⟨true, false, b2, false, b4, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, false, b4, true, true, false, b8, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, b4, true, true, false, b8, false, false, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · exact (f61 ⟨true, false, b2, false, b4, true, true, false, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, b2, false, b4, true, true, false, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, false, b4, true, true, false, b8, false, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, b4, true, true, false, b8, false, true, true, false, true⟩ rfl rfl).symm
                  · cases b10
                    · cases b4
                      · cases b13
                        · exact (f94 ⟨true, false, b2, true, false, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, false, b2, true, false, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, b2, true, false, true, true, false, b8, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, true, false, true, true, false, b8, false, false, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · exact (f52 ⟨true, false, b2, true, true, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, false, b2, true, true, true, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, b2, true, true, true, true, false, b8, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, true, true, true, true, false, b8, false, false, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · exact (f75 ⟨true, false, b2, true, b4, true, true, false, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, b4, true, true, false, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, true, b4, true, true, false, b8, false, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, true, b4, true, true, false, b8, false, true, true, false, true⟩ rfl rfl).symm
                · cases b4
                  · cases b8
                    · cases b13
                      · cases b3
                        · cases b2
                          · exact (f103 ⟨true, false, false, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f100 ⟨true, false, true, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g100 ⟨true, false, true, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f17 ⟨true, false, b2, true, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, b2, true, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, b3, false, true, true, false, false, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, false, true, true, false, false, true, b10, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b10
                        · cases b2
                          · exact (f115 ⟨true, false, false, b3, false, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, false, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f36 ⟨true, false, true, b3, false, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, false, true, b3, false, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, false, false, b3, false, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, false, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f26 ⟨true, false, true, b3, false, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, b3, false, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, b3, false, true, true, false, true, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, false, true, true, false, true, true, b10, true, false, true⟩ rfl rfl).symm
                  · cases b8
                    · cases b13
                      · exact (f7 ⟨true, false, b2, b3, true, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, false, b2, b3, true, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, b3, true, true, true, false, false, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, true, true, true, false, false, true, b10, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b2
                        · exact (f115 ⟨true, false, false, b3, true, true, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, true, true, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f36 ⟨true, false, true, b3, true, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, false, true, b3, true, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f72 ⟨true, false, true, b3, true, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g72 ⟨true, false, true, b3, true, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, b3, true, true, true, false, true, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, true, true, true, false, true, true, b10, true, false, true⟩ rfl rfl).symm
          · cases b0
            · cases b5
              · cases b8
                · cases b2
                  · cases b13
                    · cases b4
                      · exact (f56 ⟨false, true, false, b3, false, false, true, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, false, true, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f66 ⟨false, true, false, b3, true, false, true, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, false, true, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨false, true, false, b3, b4, false, true, false, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, false, b3, b4, false, true, false, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f42 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, true, b3, b4, false, true, false, false, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b2
                    · cases b4
                      · exact (f56 ⟨false, true, false, b3, false, false, true, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, false, true, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f66 ⟨false, true, false, b3, true, false, true, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, false, true, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f42 ⟨false, true, true, b3, b4, false, true, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, true, false, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f39 ⟨false, true, b2, b3, b4, false, true, false, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, b2, b3, b4, false, true, false, true, b9, b10, true, false, true⟩ rfl rfl rfl rfl).symm
              · cases b2
                · cases b4
                  · cases b13
                    · exact (f56 ⟨false, true, false, b3, false, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, true, false, b3, false, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, false, b3, false, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, false, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).symm
                  · cases b13
                    · exact (f66 ⟨false, true, false, b3, true, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, false, b3, true, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, true, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).symm
                · cases b13
                  · exact (f11 ⟨false, true, true, b3, b4, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, false, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, true, true, b3, b4, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, true, false, b8, b9, b10, true, false, true⟩ rfl rfl).symm
            · cases b9
              · cases b3
                · cases b10
                  · cases b13
                    · exact (f32 ⟨true, true, b2, false, b4, b5, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g32 ⟨true, true, b2, false, b4, b5, true, false, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · cases b5
                        · exact (f44 ⟨true, true, b2, false, b4, false, true, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, false, b4, false, true, false, false, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, b4, true, true, false, false, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, b4, true, true, false, false, false, false, true, false, true⟩ rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, true, b2, false, b4, false, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, false, b4, false, true, false, true, false, false, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, b4, true, true, false, true, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, b4, true, true, false, true, false, false, true, false, true⟩ rfl rfl).symm
                  · cases b8
                    · cases b13
                      · exact (f61 ⟨true, true, b2, false, b4, b5, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, true, b2, false, b4, b5, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f44 ⟨true, true, b2, false, b4, false, true, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, false, b4, false, true, false, false, false, true, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, b4, true, true, false, false, false, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, b4, true, true, false, false, false, true, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · exact (f61 ⟨true, true, b2, false, b4, b5, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, true, b2, false, b4, b5, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · exact (f39 ⟨true, true, b2, false, b4, false, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, false, b4, false, true, false, true, false, true, true, false, true⟩ rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, b4, true, true, false, true, false, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, b4, true, true, false, true, false, true, true, false, true⟩ rfl rfl).symm
                · cases b8
                  · cases b13
                    · cases b10
                      · cases b4
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, false, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, false, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f94 ⟨true, true, b2, true, false, true, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, true, b2, true, false, true, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, true, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, true, false, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f52 ⟨true, true, b2, true, true, true, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, true, b2, true, true, true, true, false, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, true, b2, true, b4, b5, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, true, false, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f44 ⟨true, true, b2, true, b4, false, true, false, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, true, b4, false, true, false, false, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, true, b4, true, true, false, false, false, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, b4, true, true, false, false, false, b10, true, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b10
                      · cases b4
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, false, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, false, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f94 ⟨true, true, b2, true, false, true, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, true, b2, true, false, true, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, true, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, true, false, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f52 ⟨true, true, b2, true, true, true, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, true, b2, true, true, true, true, false, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, true, b2, true, b4, b5, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, true, false, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f39 ⟨true, true, b2, true, b4, false, true, false, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, true, b4, false, true, false, true, false, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, true, b4, true, true, false, true, false, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, b4, true, true, false, true, false, b10, true, false, true⟩ rfl rfl).symm
              · cases b5
                · cases b2
                  · cases b8
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, false, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f55 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, false, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f10 ⟨true, true, true, b3, b4, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, true, true, b3, b4, false, true, false, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f44 ⟨true, true, true, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, true, b3, b4, false, true, false, false, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f39 ⟨true, true, true, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, true, b3, b4, false, true, false, true, true, b10, true, false, true⟩ rfl rfl rfl rfl).symm
                · cases b4
                  · cases b13
                    · cases b2
                      · cases b8
                        · cases b3
                          · exact (f40 ⟨true, true, false, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, false, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f45 ⟨true, true, false, true, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, false, true, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f115 ⟨true, true, false, b3, false, true, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, false, true, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b8
                        · cases b3
                          · exact (f40 ⟨true, true, true, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, true, false, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f45 ⟨true, true, true, true, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, true, true, false, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f36 ⟨true, true, true, b3, false, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, true, true, b3, false, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f114 ⟨true, true, true, b3, false, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g114 ⟨true, true, true, b3, false, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, false, true, true, false, b8, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, true, false, b8, true, b10, true, false, true⟩ rfl rfl).symm
                  · cases b8
                    · cases b13
                      · exact (f7 ⟨true, true, b2, b3, true, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, true, b2, b3, true, true, true, false, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, true, true, true, false, false, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, true, false, false, true, b10, true, false, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b2
                        · exact (f115 ⟨true, true, false, b3, true, true, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, true, true, true, false, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f36 ⟨true, true, true, b3, true, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, true, true, b3, true, true, true, false, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f86 ⟨true, true, true, b3, true, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g86 ⟨true, true, true, b3, true, true, true, false, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, true, true, true, false, true, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, true, false, true, true, b10, true, false, true⟩ rfl rfl).symm
      · cases b1
        · cases b5
          · cases b9
            · cases b8
              · cases b10
                · cases b3
                  · cases b0
                    · cases b13
                      · cases b2
                        · cases b11
                          · cases b4
                            · exact (f91 ⟨false, false, false, false, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, false, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f93 ⟨false, false, false, false, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, false, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b4
                            · exact (f91 ⟨false, false, false, false, false, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, false, false, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f66 ⟨false, false, false, false, true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, false, true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f126 ⟨false, false, true, false, b4, false, true, true, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, false, b4, false, true, true, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨false, false, b2, false, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, false, b2, false, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).symm
                    · cases b13
                      · cases b11
                        · cases b4
                          · exact (f110 ⟨true, false, b2, false, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, false, b2, false, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f102 ⟨true, false, b2, false, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, false, b2, false, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f43 ⟨true, false, b2, false, b4, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, false, b2, false, b4, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f44 ⟨true, false, b2, false, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, b2, false, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b2
                      · cases b0
                        · cases b11
                          · cases b4
                            · exact (f91 ⟨false, false, false, true, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, true, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f93 ⟨false, false, false, true, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, true, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b4
                            · exact (f91 ⟨false, false, false, true, false, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, true, false, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f66 ⟨false, false, false, true, true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, true, true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · cases b4
                            · exact (f110 ⟨true, false, false, true, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, false, false, true, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f102 ⟨true, false, false, true, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, false, false, true, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f74 ⟨true, false, false, true, b4, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, b4, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b0
                        · exact (f126 ⟨false, false, true, true, b4, false, true, true, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, true, b4, false, true, true, false, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · cases b4
                            · exact (f110 ⟨true, false, true, true, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, false, true, true, false, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f102 ⟨true, false, true, true, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, false, true, true, true, false, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f74 ⟨true, false, true, true, b4, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, true, true, b4, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨b0, false, b2, true, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨b0, false, b2, true, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b0
                    · cases b2
                      · cases b11
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f93 ⟨false, false, false, b3, true, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f66 ⟨false, false, false, b3, true, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, b4, false, true, true, false, false, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, true, false, false, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b11
                      · cases b3
                        · exact (f87 ⟨true, false, b2, false, b4, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, b2, false, b4, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, false, b2, true, b4, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, b4, false, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f61 ⟨true, false, b2, false, b4, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, b2, false, b4, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, false, b2, true, b4, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, b4, false, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f44 ⟨b0, false, b2, b3, b4, false, true, true, false, false, true, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨b0, false, b2, b3, b4, false, true, true, false, false, true, b11, false, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · cases b10
                  · cases b3
                    · cases b0
                      · cases b2
                        · cases b11
                          · cases b4
                            · exact (f91 ⟨false, false, false, false, false, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, false, false, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f93 ⟨false, false, false, false, true, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, false, true, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b4
                            · exact (f91 ⟨false, false, false, false, false, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, false, false, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f66 ⟨false, false, false, false, true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, false, true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f126 ⟨false, false, true, false, b4, false, true, true, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, false, b4, false, true, true, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b11
                        · exact (f113 ⟨true, false, b2, false, b4, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, b2, false, b4, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f43 ⟨true, false, b2, false, b4, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, false, b2, false, b4, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · cases b0
                        · cases b11
                          · cases b4
                            · exact (f91 ⟨false, false, false, true, false, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, true, false, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f93 ⟨false, false, false, true, true, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, true, true, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b4
                            · exact (f91 ⟨false, false, false, true, false, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, true, false, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f66 ⟨false, false, false, true, true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, true, true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · exact (f113 ⟨true, false, false, true, b4, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, false, true, b4, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f74 ⟨true, false, false, true, b4, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, false, true, b4, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b0
                        · exact (f126 ⟨false, false, true, true, b4, false, true, true, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, true, b4, false, true, true, true, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · exact (f113 ⟨true, false, true, true, b4, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, true, true, b4, false, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f74 ⟨true, false, true, true, b4, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, false, true, true, b4, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b0
                    · cases b2
                      · cases b11
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f93 ⟨false, false, false, b3, true, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f66 ⟨false, false, false, b3, true, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, b4, false, true, true, true, false, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, true, true, false, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b11
                      · cases b3
                        · exact (f87 ⟨true, false, b2, false, b4, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, b2, false, b4, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, false, b2, true, b4, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, b4, false, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f61 ⟨true, false, b2, false, b4, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, b2, false, b4, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, false, b2, true, b4, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, b4, false, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f39 ⟨b0, false, b2, b3, b4, false, true, true, true, false, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨b0, false, b2, b3, b4, false, true, true, true, false, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
            · cases b0
              · cases b8
                · cases b13
                  · cases b10
                    · cases b2
                      · cases b11
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f93 ⟨false, false, false, b3, true, false, true, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, true, false, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f66 ⟨false, false, false, b3, true, false, true, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, true, false, true, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f65 ⟨false, false, true, b3, b4, false, true, true, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, true, true, false, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · cases b11
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f93 ⟨false, false, false, b3, true, false, true, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, true, false, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f66 ⟨false, false, false, b3, true, false, true, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, true, false, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, b4, false, true, true, false, true, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, true, false, true, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f44 ⟨false, false, b2, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, false, b2, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b10
                    · cases b2
                      · cases b11
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f93 ⟨false, false, false, b3, true, false, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f66 ⟨false, false, false, b3, true, false, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f65 ⟨false, false, true, b3, b4, false, true, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, true, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · cases b11
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f93 ⟨false, false, false, b3, true, false, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, false, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f91 ⟨false, false, false, b3, false, false, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, false, false, b3, false, false, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f66 ⟨false, false, false, b3, true, false, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, false, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, b4, false, true, true, true, true, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, true, true, true, true, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f39 ⟨false, false, b2, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, false, b2, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · cases b4
                  · cases b2
                    · cases b3
                      · exact (f123 ⟨true, false, false, false, false, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g123 ⟨true, false, false, false, false, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b8
                        · exact (f41 ⟨true, false, false, true, false, false, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g41 ⟨true, false, false, true, false, false, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f48 ⟨true, false, false, true, false, false, true, true, true, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g48 ⟨true, false, false, true, false, false, true, true, true, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · cases b11
                        · exact (f78 ⟨true, false, true, false, false, false, true, true, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g78 ⟨true, false, true, false, false, false, true, true, b8, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f101 ⟨true, false, true, false, false, false, true, true, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g101 ⟨true, false, true, false, false, false, true, true, b8, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f12 ⟨true, false, true, true, false, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g12 ⟨true, false, true, true, false, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  · exact (f5 ⟨true, false, b2, b3, true, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g5 ⟨true, false, b2, b3, true, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                · cases b8
                  · exact (f44 ⟨true, false, b2, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, false, b2, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f39 ⟨true, false, b2, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, false, b2, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
          · cases b0
            · cases b2
              · cases b13
                · cases b4
                  · exact (f54 ⟨false, false, false, b3, false, true, true, true, b8, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, false, false, b3, false, true, true, true, b8, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · exact (f93 ⟨false, false, false, b3, true, true, true, true, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, false, false, b3, true, true, true, true, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, false, false, b3, true, true, true, true, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, false, false, b3, true, true, true, true, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, false, false, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨false, false, false, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).symm
              · cases b13
                · cases b10
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, true, true, true, b8, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, true, true, true, b8, false, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, true, true, true, b8, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, true, true, true, b8, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f85 ⟨false, false, true, b3, b4, true, true, true, b8, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, true, true, true, b8, b9, true, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, false, true, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).symm
            · cases b9
              · cases b10
                · cases b3
                  · cases b13
                    · cases b11
                      · cases b8
                        · cases b4
                          · exact (f110 ⟨true, false, b2, false, false, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, false, b2, false, false, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f102 ⟨true, false, b2, false, true, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, false, b2, false, true, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f113 ⟨true, false, b2, false, b4, true, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, b2, false, b4, true, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f43 ⟨true, false, b2, false, b4, true, true, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, false, b2, false, b4, true, true, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, b2, false, b4, true, true, true, b8, false, false, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, b4, true, true, true, b8, false, false, b11, false, true⟩ rfl rfl).symm
                  · cases b11
                    · cases b13
                      · cases b8
                        · cases b4
                          · exact (f110 ⟨true, false, b2, true, false, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, false, b2, true, false, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f102 ⟨true, false, b2, true, true, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, false, b2, true, true, true, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f113 ⟨true, false, b2, true, b4, true, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, false, b2, true, b4, true, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, false, b2, true, b4, true, true, true, b8, false, false, false, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, true, b4, true, true, true, b8, false, false, false, false, true⟩ rfl rfl).symm
                    · cases b4
                      · cases b13
                        · exact (f94 ⟨true, false, b2, true, false, true, true, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, false, b2, true, false, true, true, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, b2, true, false, true, true, true, b8, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, true, false, true, true, true, b8, false, false, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · exact (f52 ⟨true, false, b2, true, true, true, true, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, false, b2, true, true, true, true, true, b8, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, b2, true, true, true, true, true, b8, false, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, true, true, true, true, true, b8, false, false, true, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b11
                    · cases b3
                      · exact (f87 ⟨true, false, b2, false, b4, true, true, true, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, false, b2, false, b4, true, true, true, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, false, b2, true, b4, true, true, true, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, b4, true, true, true, b8, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f61 ⟨true, false, b2, false, b4, true, true, true, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, false, b2, false, b4, true, true, true, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, false, b2, true, b4, true, true, true, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, false, b2, true, b4, true, true, true, b8, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, false, b2, b3, b4, true, true, true, b8, false, true, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, b4, true, true, true, b8, false, true, b11, false, true⟩ rfl rfl).symm
              · cases b4
                · cases b8
                  · cases b13
                    · cases b11
                      · cases b3
                        · exact (f90 ⟨true, false, b2, false, false, true, true, true, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g90 ⟨true, false, b2, false, false, true, true, true, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f15 ⟨true, false, b2, true, false, true, true, true, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g15 ⟨true, false, b2, true, false, true, true, true, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b2
                          · exact (f103 ⟨true, false, false, false, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f100 ⟨true, false, true, false, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g100 ⟨true, false, true, false, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f17 ⟨true, false, b2, true, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, b2, true, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, b2, b3, false, true, true, true, false, true, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, false, true, true, true, false, true, b10, b11, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b3
                      · cases b10
                        · cases b2
                          · exact (f115 ⟨true, false, false, false, false, true, true, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, false, true, true, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b11
                            · exact (f98 ⟨true, false, true, false, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, false, true, false, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f108 ⟨true, false, true, false, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, false, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, false, false, false, false, true, true, true, true, true, true, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, false, true, true, true, true, true, true, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b11
                            · exact (f105 ⟨true, false, true, false, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g105 ⟨true, false, true, false, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, false, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, false, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b11
                        · cases b10
                          · cases b2
                            · exact (f115 ⟨true, false, false, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f50 ⟨true, false, true, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, false, true, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, false, false, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f105 ⟨true, false, true, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g105 ⟨true, false, true, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, false, false, true, false, true, true, true, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, true, true, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f108 ⟨true, false, true, true, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, true, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, true, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, true, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, b2, b3, false, true, true, true, true, true, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, false, true, true, true, true, true, b10, b11, false, true⟩ rfl rfl).symm
                · cases b8
                  · cases b13
                    · exact (f7 ⟨true, false, b2, b3, true, true, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, false, b2, b3, true, true, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, b2, b3, true, true, true, true, false, true, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, true, true, true, true, false, true, b10, b11, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b3
                      · cases b10
                        · cases b2
                          · exact (f115 ⟨true, false, false, false, true, true, true, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, true, true, true, true, false, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b11
                            · exact (f98 ⟨true, false, true, false, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, false, true, false, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f108 ⟨true, false, true, false, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, false, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b11
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f51 ⟨true, false, true, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, false, true, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, false, false, false, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, false, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, false, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b11
                        · cases b10
                          · cases b2
                            · exact (f115 ⟨true, false, false, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f50 ⟨true, false, true, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, false, true, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, false, false, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f51 ⟨true, false, true, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, false, true, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, false, false, true, true, true, true, true, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, true, true, true, true, true, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f108 ⟨true, false, true, true, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, true, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f125 ⟨true, false, true, true, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, true, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, false, b2, b3, true, true, true, true, true, true, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, true, true, true, true, true, true, b10, b11, false, true⟩ rfl rfl).symm
        · cases b0
          · cases b5
            · cases b8
              · cases b2
                · cases b13
                  · cases b11
                    · cases b4
                      · exact (f91 ⟨false, true, false, b3, false, false, true, true, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, true, true, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, false, true, true, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, false, true, true, false, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · exact (f91 ⟨false, true, false, b3, false, false, true, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, true, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f66 ⟨false, true, false, b3, true, false, true, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, false, true, true, false, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f44 ⟨false, true, false, b3, b4, false, true, true, false, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, false, b3, b4, false, true, true, false, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f42 ⟨false, true, true, b3, b4, false, true, true, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, true, true, false, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f44 ⟨false, true, true, b3, b4, false, true, true, false, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨false, true, true, b3, b4, false, true, true, false, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · cases b2
                  · cases b11
                    · cases b4
                      · exact (f91 ⟨false, true, false, b3, false, false, true, true, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, true, true, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f93 ⟨false, true, false, b3, true, false, true, true, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, false, true, true, true, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · exact (f91 ⟨false, true, false, b3, false, false, true, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, true, false, b3, false, false, true, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f66 ⟨false, true, false, b3, true, false, true, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, false, true, true, true, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f42 ⟨false, true, true, b3, b4, false, true, true, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, true, true, true, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f39 ⟨false, true, b2, b3, b4, false, true, true, true, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨false, true, b2, b3, b4, false, true, true, true, b9, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
            · cases b2
              · cases b13
                · cases b4
                  · exact (f54 ⟨false, true, false, b3, false, true, true, true, b8, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, true, false, b3, false, true, true, true, b8, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · exact (f93 ⟨false, true, false, b3, true, true, true, true, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g93 ⟨false, true, false, b3, true, true, true, true, b8, b9, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f66 ⟨false, true, false, b3, true, true, true, true, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, true, false, b3, true, true, true, true, b8, b9, b10, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, true, false, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨false, true, false, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).symm
              · cases b13
                · exact (f11 ⟨false, true, true, b3, b4, true, true, true, b8, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, true, b8, b9, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, true, true, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, true, true, b8, b9, b10, b11, false, true⟩ rfl rfl).symm
          · cases b9
            · cases b8
              · cases b10
                · cases b3
                  · cases b13
                    · cases b11
                      · cases b4
                        · exact (f110 ⟨true, true, b2, false, false, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, true, b2, false, false, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f102 ⟨true, true, b2, false, true, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, true, b2, false, true, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f43 ⟨true, true, b2, false, b4, b5, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, true, b2, false, b4, b5, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f44 ⟨true, true, b2, false, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, false, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, false, b4, true, true, true, false, false, false, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, b4, true, true, true, false, false, false, b11, false, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b11
                      · cases b4
                        · exact (f110 ⟨true, true, b2, true, false, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, true, b2, true, false, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f102 ⟨true, true, b2, true, true, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, true, b2, true, true, b5, true, true, false, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, false, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, false, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f94 ⟨true, true, b2, true, false, true, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, true, b2, true, false, true, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, true, false, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f52 ⟨true, true, b2, true, true, true, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, true, b2, true, true, true, true, true, false, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · exact (f44 ⟨true, true, b2, true, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, true, b4, false, true, true, false, false, false, b11, false, true⟩ rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, true, b4, true, true, true, false, false, false, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, b4, true, true, true, false, false, false, b11, false, true⟩ rfl rfl).symm
                · cases b13
                  · cases b11
                    · cases b3
                      · exact (f87 ⟨true, true, b2, false, b4, b5, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, true, b2, false, b4, b5, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, true, b2, true, b4, b5, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, true, true, false, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f61 ⟨true, true, b2, false, b4, b5, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, true, b2, false, b4, b5, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, true, b2, true, b4, b5, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, true, true, false, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · exact (f44 ⟨true, true, b2, b3, b4, false, true, true, false, false, true, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, b2, b3, b4, false, true, true, false, false, true, b11, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, b4, true, true, true, false, false, true, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, b4, true, true, true, false, false, true, b11, false, true⟩ rfl rfl).symm
              · cases b13
                · cases b10
                  · cases b3
                    · cases b11
                      · exact (f113 ⟨true, true, b2, false, b4, b5, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, true, b2, false, b4, b5, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f43 ⟨true, true, b2, false, b4, b5, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, true, b2, false, b4, b5, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b11
                      · exact (f113 ⟨true, true, b2, true, b4, b5, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, true, b2, true, b4, b5, true, true, true, false, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, false, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, false, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f94 ⟨true, true, b2, true, false, true, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, true, b2, true, false, true, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f74 ⟨true, true, b2, true, true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, true, b2, true, true, false, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f52 ⟨true, true, b2, true, true, true, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, true, b2, true, true, true, true, true, true, false, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b11
                    · cases b3
                      · exact (f87 ⟨true, true, b2, false, b4, b5, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, true, b2, false, b4, b5, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, true, b2, true, b4, b5, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, true, true, true, false, true, false, false, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f61 ⟨true, true, b2, false, b4, b5, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, true, b2, false, b4, b5, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, true, b2, true, b4, b5, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, true, b2, true, b4, b5, true, true, true, false, true, true, false, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b5
                  · exact (f39 ⟨true, true, b2, b3, b4, false, true, true, true, false, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, b2, b3, b4, false, true, true, true, false, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, true, b2, b3, b4, true, true, true, true, false, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, b4, true, true, true, true, false, b10, b11, false, true⟩ rfl rfl).symm
            · cases b5
              · cases b2
                · cases b8
                  · cases b13
                    · exact (f55 ⟨true, true, false, b3, b4, false, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f44 ⟨true, true, false, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, false, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f55 ⟨true, true, false, b3, b4, false, true, true, true, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g55 ⟨true, true, false, b3, b4, false, true, true, true, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f39 ⟨true, true, false, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, false, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f10 ⟨true, true, true, b3, b4, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g10 ⟨true, true, true, b3, b4, false, true, true, b8, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · exact (f44 ⟨true, true, true, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g44 ⟨true, true, true, b3, b4, false, true, true, false, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
                    · exact (f39 ⟨true, true, true, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).trans (g39 ⟨true, true, true, b3, b4, false, true, true, true, true, b10, b11, false, true⟩ rfl rfl rfl rfl).symm
              · cases b4
                · cases b8
                  · cases b11
                    · cases b13
                      · exact (f111 ⟨true, true, b2, b3, false, true, true, true, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g111 ⟨true, true, b2, b3, false, true, true, true, false, true, b10, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, false, true, true, true, false, true, b10, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, true, true, false, true, b10, false, false, true⟩ rfl rfl).symm
                    · cases b3
                      · cases b13
                        · exact (f40 ⟨true, true, b2, false, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, b2, false, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, false, false, true, true, true, false, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, false, true, true, true, false, true, b10, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · exact (f45 ⟨true, true, b2, true, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, b2, true, false, true, true, true, false, true, b10, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, true, false, true, true, true, false, true, b10, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, true, false, true, true, true, false, true, b10, true, false, true⟩ rfl rfl).symm
                  · cases b11
                    · cases b13
                      · cases b3
                        · cases b10
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f98 ⟨true, true, true, false, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, true, true, false, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f105 ⟨true, true, true, false, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g105 ⟨true, true, true, false, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · cases b2
                            · exact (f115 ⟨true, true, false, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f50 ⟨true, true, true, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, true, true, true, false, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, true, false, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f105 ⟨true, true, true, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g105 ⟨true, true, true, true, false, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, false, true, true, true, true, true, b10, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, true, true, true, true, b10, false, false, true⟩ rfl rfl).symm
                    · cases b10
                      · cases b13
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f24 ⟨true, true, true, b3, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, b3, false, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, false, true, true, true, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, true, true, true, true, false, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f125 ⟨true, true, true, b3, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, true, true, b3, false, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, false, true, true, true, true, true, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, false, true, true, true, true, true, true, true, false, true⟩ rfl rfl).symm
                · cases b8
                  · cases b13
                    · exact (f7 ⟨true, true, b2, b3, true, true, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g7 ⟨true, true, b2, b3, true, true, true, true, false, true, b10, b11, false, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, true, true, true, true, false, true, b10, b11, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, true, true, false, true, b10, b11, false, true⟩ rfl rfl).symm
                  · cases b11
                    · cases b13
                      · cases b3
                        · cases b10
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f98 ⟨true, true, true, false, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, true, true, false, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f51 ⟨true, true, true, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, true, true, false, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · cases b2
                            · exact (f115 ⟨true, true, false, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f50 ⟨true, true, true, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, true, true, true, true, true, true, true, true, true, false, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, true, false, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f51 ⟨true, true, true, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, true, true, true, true, true, true, true, true, true, true, false, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, b3, true, true, true, true, true, true, b10, false, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, true, true, true, true, b10, false, false, true⟩ rfl rfl).symm
                    · cases b10
                      · cases b13
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f24 ⟨true, true, true, b3, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, b3, true, true, true, true, true, true, false, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, true, true, true, true, true, true, false, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, true, true, true, true, false, true, false, true⟩ rfl rfl).symm
                      · cases b13
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f125 ⟨true, true, true, b3, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, true, true, b3, true, true, true, true, true, true, true, true, false, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, true, b2, b3, true, true, true, true, true, true, true, true, false, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, true, true, true, true, true, true, true, true, false, true⟩ rfl rfl).symm
  · cases b7
    · cases b11
      · cases b5
        · cases b0
          · cases b2
            · cases b4
              · cases b13
                · exact (f56 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · exact (f121 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).symm
              · cases b10
                · cases b13
                  · exact (f84 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f121 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f84 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).symm
            · cases b1
              · cases b10
                · cases b13
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, false, b6, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, false, b6, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, false, b6, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, b6, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f122 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f85 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · exact (f42 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · exact (f122 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, true, false, true, true⟩ rfl rfl rfl rfl).symm
          · cases b9
            · cases b4
              · cases b3
                · cases b8
                  · cases b10
                    · cases b6
                      · cases b13
                        · exact (f47 ⟨true, b1, b2, false, false, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, b1, b2, false, false, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f121 ⟨true, b1, false, false, false, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f122 ⟨true, b1, true, false, false, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, false, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · cases b13
                        · exact (f110 ⟨true, b1, b2, false, false, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, b1, b2, false, false, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f121 ⟨true, b1, false, false, false, false, true, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, true, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                          · exact (f122 ⟨true, b1, true, false, false, false, true, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, true, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f87 ⟨true, b1, b2, false, false, false, b6, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, false, false, b6, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f73 ⟨true, b1, b2, false, false, false, b6, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, false, false, false, b6, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b10
                      · cases b6
                        · exact (f60 ⟨true, b1, b2, false, false, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, b1, b2, false, false, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f113 ⟨true, b1, b2, false, false, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, false, false, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f87 ⟨true, b1, b2, false, false, false, b6, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, false, false, b6, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · cases b2
                        · exact (f121 ⟨true, b1, false, false, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, false, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f73 ⟨true, b1, b2, false, false, false, b6, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, false, false, false, b6, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
                · cases b8
                  · cases b10
                    · cases b13
                      · cases b6
                        · exact (f77 ⟨true, b1, b2, true, false, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, b1, b2, true, false, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f110 ⟨true, b1, b2, true, false, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, b1, b2, true, false, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, true, false, false, b6, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, false, false, b6, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, true, false, false, b6, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, false, false, b6, false, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f75 ⟨true, b1, b2, true, false, false, b6, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, false, false, b6, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f73 ⟨true, b1, b2, true, false, false, b6, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, true, false, false, b6, false, false, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b10
                      · cases b6
                        · exact (f60 ⟨true, b1, b2, true, false, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, b1, b2, true, false, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f113 ⟨true, b1, b2, true, false, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, true, false, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, b1, b2, true, false, false, b6, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, false, false, b6, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · cases b2
                        · exact (f121 ⟨true, b1, false, true, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, true, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, false, false, b6, false, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f73 ⟨true, b1, b2, true, false, false, b6, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, true, false, false, b6, false, true, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · cases b10
                  · cases b8
                    · cases b3
                      · cases b6
                        · exact (f47 ⟨true, b1, b2, false, true, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, b1, b2, false, true, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f102 ⟨true, b1, b2, false, true, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, b1, b2, false, true, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b6
                        · exact (f77 ⟨true, b1, b2, true, true, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, b1, b2, true, true, false, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f102 ⟨true, b1, b2, true, true, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, b1, b2, true, true, false, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b6
                      · exact (f3 ⟨true, b1, b2, b3, true, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g3 ⟨true, b1, b2, b3, true, false, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f113 ⟨true, b1, b2, b3, true, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, b3, true, false, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b3
                    · exact (f87 ⟨true, b1, b2, false, true, false, b6, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, true, false, b6, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f75 ⟨true, b1, b2, true, true, false, b6, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, true, false, b6, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · cases b2
                    · exact (f121 ⟨true, b1, false, b3, true, false, b6, false, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, true, false, b6, false, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f122 ⟨true, b1, true, b3, true, false, b6, false, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, true, false, b6, false, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨true, b1, b2, b3, true, false, b6, false, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, b3, true, false, b6, false, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
            · cases b10
              · cases b13
                · cases b4
                  · exact (f112 ⟨true, b1, b2, b3, false, false, b6, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, b2, b3, false, false, b6, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f80 ⟨true, b1, b2, b3, true, false, b6, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, b1, b2, b3, true, false, b6, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                · cases b2
                  · exact (f121 ⟨true, b1, false, b3, b4, false, b6, false, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, b4, false, b6, false, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f122 ⟨true, b1, true, b3, b4, false, b6, false, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, b4, false, b6, false, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
              · cases b13
                · cases b4
                  · exact (f112 ⟨true, b1, b2, b3, false, false, b6, false, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, b2, b3, false, false, b6, false, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f80 ⟨true, b1, b2, b3, true, false, b6, false, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, b1, b2, b3, true, false, b6, false, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                · exact (f73 ⟨true, b1, b2, b3, b4, false, b6, false, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, b3, b4, false, b6, false, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
        · cases b6
          · cases b13
            · cases b0
              · cases b2
                · cases b4
                  · exact (f56 ⟨false, b1, false, b3, false, true, false, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, b1, false, b3, false, true, false, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f84 ⟨false, b1, false, b3, true, true, false, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, true, false, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b1
                  · cases b10
                    · cases b9
                      · exact (f126 ⟨false, false, true, b3, b4, true, false, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, true, false, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f65 ⟨false, false, true, b3, b4, true, false, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, true, false, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f85 ⟨false, false, true, b3, b4, true, false, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, true, false, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f29 ⟨false, true, true, b3, b4, true, false, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
              · cases b2
                · cases b9
                  · cases b8
                    · cases b3
                      · cases b10
                        · exact (f63 ⟨true, b1, false, false, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g63 ⟨true, b1, false, false, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f87 ⟨true, b1, false, false, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, false, false, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · exact (f77 ⟨true, b1, false, true, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, b1, false, true, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, b1, false, true, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, false, true, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · cases b4
                        · exact (f60 ⟨true, b1, false, b3, false, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, b1, false, b3, false, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f70 ⟨true, b1, false, b3, true, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g70 ⟨true, b1, false, b3, true, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f87 ⟨true, b1, false, false, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, false, false, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, b1, false, true, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, false, true, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b4
                      · exact (f64 ⟨true, b1, false, b3, false, true, false, false, false, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, b1, false, b3, false, true, false, false, false, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, b1, false, b3, true, true, false, false, false, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, false, b3, true, true, false, false, false, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f115 ⟨true, b1, false, b3, b4, true, false, false, true, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, b3, b4, true, false, false, true, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b10
                  · cases b9
                    · cases b8
                      · cases b3
                        · exact (f63 ⟨true, b1, true, false, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g63 ⟨true, b1, true, false, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f77 ⟨true, b1, true, true, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g77 ⟨true, b1, true, true, b4, true, false, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · exact (f60 ⟨true, b1, true, b3, false, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g60 ⟨true, b1, true, b3, false, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f70 ⟨true, b1, true, b3, true, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g70 ⟨true, b1, true, b3, true, true, false, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · cases b4
                        · exact (f64 ⟨true, b1, true, b3, false, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, b1, true, b3, false, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f49 ⟨true, b1, true, b3, true, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, true, b3, true, true, false, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · exact (f98 ⟨true, b1, true, false, b4, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, b1, true, false, b4, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f50 ⟨true, b1, true, true, b4, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, b1, true, true, b4, true, false, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b9
                      · cases b3
                        · exact (f87 ⟨true, b1, true, false, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, true, false, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, b1, true, true, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, true, true, b4, true, false, false, false, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · exact (f64 ⟨true, b1, true, b3, false, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, b1, true, b3, false, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f49 ⟨true, b1, true, b3, true, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, true, b3, true, true, false, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b9
                      · cases b3
                        · exact (f87 ⟨true, b1, true, false, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, true, false, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f75 ⟨true, b1, true, true, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, true, true, b4, true, false, false, true, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · exact (f119 ⟨true, b1, true, b3, false, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g119 ⟨true, b1, true, b3, false, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · cases b1
                            · exact (f117 ⟨true, false, true, false, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g117 ⟨true, false, true, false, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f53 ⟨true, true, true, false, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g53 ⟨true, true, true, false, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b1
                            · exact (f20 ⟨true, false, true, true, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g20 ⟨true, false, true, true, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f127 ⟨true, true, true, true, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g127 ⟨true, true, true, true, true, true, false, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
            · exact (f59 ⟨b0, b1, b2, b3, b4, true, false, false, b8, b9, b10, false, true, true⟩ rfl rfl).trans (g59 ⟨b0, b1, b2, b3, b4, true, false, false, b8, b9, b10, false, true, true⟩ rfl rfl).symm
          · cases b13
            · cases b4
              · cases b0
                · cases b2
                  · exact (f56 ⟨false, b1, false, b3, false, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, b1, false, b3, false, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b1
                    · cases b10
                      · cases b9
                        · exact (f126 ⟨false, false, true, b3, false, true, true, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, false, true, true, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f65 ⟨false, false, true, b3, false, true, true, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, false, true, true, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, false, true, true, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, false, true, true, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f11 ⟨false, true, true, b3, false, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, false, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b9
                  · cases b10
                    · cases b8
                      · exact (f110 ⟨true, b1, b2, b3, false, true, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, b1, b2, b3, false, true, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f113 ⟨true, b1, b2, b3, false, true, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, b3, false, true, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f87 ⟨true, b1, b2, false, false, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, false, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, b1, b2, true, false, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, false, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b10
                    · cases b8
                      · exact (f64 ⟨true, b1, b2, b3, false, true, true, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, b1, b2, b3, false, true, true, false, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b3
                        · cases b2
                          · exact (f115 ⟨true, b1, false, false, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f98 ⟨true, b1, true, false, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, b1, true, false, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, b1, false, true, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, true, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f50 ⟨true, b1, true, true, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, b1, true, true, false, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · exact (f64 ⟨true, b1, b2, b3, false, true, true, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g64 ⟨true, b1, b2, b3, false, true, true, false, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, b1, false, b3, false, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, b3, false, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f1 ⟨true, b1, true, b3, false, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g1 ⟨true, b1, true, b3, false, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
              · cases b0
                · cases b2
                  · exact (f84 ⟨false, b1, false, b3, true, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b1
                    · cases b10
                      · cases b9
                        · exact (f126 ⟨false, false, true, b3, true, true, true, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, true, true, true, false, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f65 ⟨false, false, true, b3, true, true, true, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, true, true, true, false, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f85 ⟨false, false, true, b3, true, true, true, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, true, true, true, false, b8, b9, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f11 ⟨false, true, true, b3, true, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, true, true, true, false, b8, b9, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b9
                  · cases b10
                    · cases b8
                      · exact (f102 ⟨true, b1, b2, b3, true, true, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, b1, b2, b3, true, true, true, false, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f113 ⟨true, b1, b2, b3, true, true, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, b3, true, true, true, false, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · exact (f87 ⟨true, b1, b2, false, true, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, true, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f75 ⟨true, b1, b2, true, true, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, true, true, true, false, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · exact (f49 ⟨true, b1, b2, b3, true, true, true, false, false, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, b2, b3, true, true, true, false, false, true, b10, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · cases b10
                        · cases b2
                          · exact (f115 ⟨true, b1, false, false, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f98 ⟨true, b1, true, false, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, b1, true, false, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, b1, false, false, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f51 ⟨true, b1, true, false, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, b1, true, false, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b10
                        · cases b2
                          · exact (f115 ⟨true, b1, false, true, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, true, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f50 ⟨true, b1, true, true, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, b1, true, true, true, true, true, false, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, b1, false, true, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, true, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f51 ⟨true, b1, true, true, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, b1, true, true, true, true, true, false, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
            · exact (f59 ⟨b0, b1, b2, b3, b4, true, true, false, b8, b9, b10, false, true, true⟩ rfl rfl).trans (g59 ⟨b0, b1, b2, b3, b4, true, true, false, b8, b9, b10, false, true, true⟩ rfl rfl).symm
      · cases b0
        · cases b5
          · cases b2
            · cases b4
              · cases b13
                · exact (f56 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · exact (f121 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, b1, false, b3, false, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · exact (f66 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · exact (f121 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, b1, false, b3, true, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).symm
            · cases b1
              · cases b10
                · cases b13
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, false, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, false, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, false, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f122 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f85 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, false, true, b3, b4, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · exact (f42 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · exact (f122 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, true, true, b3, b4, false, b6, false, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).symm
          · cases b2
            · cases b4
              · cases b13
                · exact (f56 ⟨false, b1, false, b3, false, true, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g56 ⟨false, b1, false, b3, false, true, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, b1, false, b3, false, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨false, b1, false, b3, false, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).symm
              · cases b13
                · exact (f66 ⟨false, b1, false, b3, true, true, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, b1, false, b3, true, true, b6, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, b1, false, b3, true, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨false, b1, false, b3, true, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).symm
            · cases b1
              · cases b13
                · cases b10
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, true, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, true, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, true, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, true, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f85 ⟨false, false, true, b3, b4, true, b6, false, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, true, b6, false, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, false, true, b3, b4, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).symm
              · cases b13
                · cases b6
                  · exact (f29 ⟨false, true, true, b3, b4, true, false, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f11 ⟨false, true, true, b3, b4, true, true, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, false, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, true, true, b3, b4, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, b6, false, b8, b9, b10, true, true, true⟩ rfl rfl).symm
        · cases b9
          · cases b3
            · cases b4
              · cases b10
                · cases b5
                  · cases b6
                    · cases b13
                      · cases b2
                        · exact (f25 ⟨true, b1, false, false, false, false, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, b1, false, false, false, false, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f116 ⟨true, b1, true, false, false, false, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g116 ⟨true, b1, true, false, false, false, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, false, false, false, false, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, false, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, false, false, false, false, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, false, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f68 ⟨true, b1, b2, false, false, false, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g68 ⟨true, b1, b2, false, false, false, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, false, false, false, true, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, true, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, false, false, false, true, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, true, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b6
                      · cases b2
                        · exact (f46 ⟨true, b1, false, false, false, true, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g46 ⟨true, b1, false, false, false, true, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f19 ⟨true, b1, true, false, false, true, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, b1, true, false, false, true, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f107 ⟨true, b1, b2, false, false, true, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g107 ⟨true, b1, b2, false, false, true, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, false, false, true, b6, false, b8, false, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, false, true, b6, false, b8, false, false, true, true, true⟩ rfl rfl).symm
                · cases b5
                  · cases b13
                    · exact (f61 ⟨true, b1, b2, false, false, false, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, false, false, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨true, b1, b2, false, false, false, b6, false, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, false, false, false, b6, false, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f61 ⟨true, b1, b2, false, false, true, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, false, true, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, false, false, true, b6, false, b8, false, true, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, false, true, b6, false, b8, false, true, true, true, true⟩ rfl rfl).symm
              · cases b13
                · cases b6
                  · cases b10
                    · cases b5
                      · exact (f8 ⟨true, b1, b2, false, true, false, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, b1, b2, false, true, false, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · cases b8
                          · exact (f76 ⟨true, b1, false, false, true, true, false, false, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g76 ⟨true, b1, false, false, true, true, false, false, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f30 ⟨true, b1, false, false, true, true, false, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g30 ⟨true, b1, false, false, true, true, false, false, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f19 ⟨true, b1, true, false, true, true, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, b1, true, false, true, true, false, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f61 ⟨true, b1, b2, false, true, b5, false, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, true, b5, false, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b10
                    · cases b5
                      · exact (f68 ⟨true, b1, b2, false, true, false, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g68 ⟨true, b1, b2, false, true, false, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f107 ⟨true, b1, b2, false, true, true, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g107 ⟨true, b1, b2, false, true, true, true, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f61 ⟨true, b1, b2, false, true, b5, true, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, true, b5, true, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b5
                  · cases b10
                    · cases b2
                      · exact (f121 ⟨true, b1, false, false, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, false, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨true, b1, b2, false, true, false, b6, false, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, false, true, false, b6, false, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, b1, b2, false, true, true, b6, false, b8, false, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, true, true, b6, false, b8, false, b10, true, true, true⟩ rfl rfl).symm
            · cases b10
              · cases b4
                · cases b5
                  · cases b13
                    · exact (f74 ⟨true, b1, b2, true, false, false, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, b1, b2, true, false, false, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · exact (f121 ⟨true, b1, false, true, false, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, false, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, true, false, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, false, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f94 ⟨true, b1, b2, true, false, true, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, b1, b2, true, false, true, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, true, false, true, b6, false, b8, false, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, false, true, b6, false, b8, false, false, true, true, true⟩ rfl rfl).symm
                · cases b13
                  · cases b5
                    · exact (f74 ⟨true, b1, b2, true, true, false, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, b1, b2, true, true, false, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f52 ⟨true, b1, b2, true, true, true, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, b1, b2, true, true, true, b6, false, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · cases b2
                      · exact (f121 ⟨true, b1, false, true, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, true, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, true, false, b6, false, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, true, true, true, b6, false, b8, false, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, true, true, b6, false, b8, false, false, true, true, true⟩ rfl rfl).symm
              · cases b5
                · cases b13
                  · exact (f75 ⟨true, b1, b2, true, b4, false, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, b4, false, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨true, b1, b2, true, b4, false, b6, false, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, true, b4, false, b6, false, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f75 ⟨true, b1, b2, true, b4, true, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, b4, true, b6, false, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, b1, b2, true, b4, true, b6, false, b8, false, true, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, b4, true, b6, false, b8, false, true, true, true, true⟩ rfl rfl).symm
          · cases b3
            · cases b5
              · cases b10
                · cases b4
                  · cases b13
                    · exact (f112 ⟨true, b1, b2, false, false, false, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, b2, false, false, false, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · exact (f121 ⟨true, b1, false, false, false, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, false, false, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f88 ⟨true, b1, b2, false, true, false, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, b2, false, true, false, b6, false, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · exact (f121 ⟨true, b1, false, false, true, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, true, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, false, true, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, true, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b13
                  · cases b4
                    · exact (f112 ⟨true, b1, b2, false, false, false, b6, false, b8, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, b2, false, false, false, b6, false, b8, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f88 ⟨true, b1, b2, false, true, false, b6, false, b8, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, b2, false, true, false, b6, false, b8, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨true, b1, b2, false, b4, false, b6, false, b8, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, false, b4, false, b6, false, b8, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
              · cases b10
                · cases b8
                  · cases b1
                    · cases b4
                      · cases b13
                        · cases b2
                          · exact (f103 ⟨true, false, false, false, false, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f100 ⟨true, false, true, false, false, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g100 ⟨true, false, true, false, false, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, b2, false, false, true, b6, false, false, true, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, false, true, b6, false, false, true, false, true, true, true⟩ rfl rfl).symm
                      · cases b13
                        · exact (f49 ⟨true, false, b2, false, true, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, false, b2, false, true, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f59 ⟨true, false, b2, false, true, true, b6, false, false, true, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, false, true, true, b6, false, false, true, false, true, true, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b4
                        · exact (f40 ⟨true, true, b2, false, false, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, b2, false, false, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f49 ⟨true, true, b2, false, true, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, true, b2, false, true, true, b6, false, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, true, b2, false, b4, true, b6, false, false, true, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, false, b4, true, b6, false, false, true, false, true, true, true⟩ rfl rfl).symm
                  · cases b6
                    · cases b13
                      · cases b2
                        · exact (f115 ⟨true, b1, false, false, b4, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, b4, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f14 ⟨true, b1, true, false, b4, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g14 ⟨true, b1, true, false, b4, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, b1, b2, false, b4, true, false, false, true, true, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, b4, true, false, false, true, true, false, true, true, true⟩ rfl rfl).symm
                    · cases b13
                      · cases b2
                        · exact (f115 ⟨true, b1, false, false, b4, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, false, b4, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f36 ⟨true, b1, true, false, b4, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, b1, true, false, b4, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, b1, b2, false, b4, true, true, false, true, true, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, b4, true, true, false, true, true, false, true, true, true⟩ rfl rfl).symm
                · cases b13
                  · cases b1
                    · cases b4
                      · cases b8
                        · cases b2
                          · exact (f103 ⟨true, false, false, false, false, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f100 ⟨true, false, true, false, false, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g100 ⟨true, false, true, false, false, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, false, false, false, false, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, false, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f26 ⟨true, false, true, false, false, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, false, false, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b8
                        · exact (f49 ⟨true, false, b2, false, true, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, false, b2, false, true, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · exact (f115 ⟨true, false, false, false, true, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, true, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f72 ⟨true, false, true, false, true, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g72 ⟨true, false, true, false, true, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b8
                      · cases b4
                        · exact (f40 ⟨true, true, b2, false, false, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, b2, false, false, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f49 ⟨true, true, b2, false, true, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, true, b2, false, true, true, b6, false, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, true, false, false, b4, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, b4, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f114 ⟨true, true, true, false, false, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g114 ⟨true, true, true, false, false, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f86 ⟨true, true, true, false, true, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g86 ⟨true, true, true, false, true, true, b6, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, b1, b2, false, b4, true, b6, false, b8, true, true, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, b4, true, b6, false, b8, true, true, true, true, true⟩ rfl rfl).symm
            · cases b13
              · cases b6
                · cases b2
                  · cases b8
                    · cases b5
                      · cases b4
                        · exact (f112 ⟨true, b1, false, true, false, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, false, true, false, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f88 ⟨true, b1, false, true, true, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, false, true, true, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b1
                          · exact (f17 ⟨true, false, false, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, false, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f45 ⟨true, true, false, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, false, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f49 ⟨true, b1, false, true, true, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, false, true, true, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · cases b4
                        · exact (f112 ⟨true, b1, false, true, false, false, false, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, false, true, false, false, false, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f88 ⟨true, b1, false, true, true, false, false, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, false, true, true, false, false, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f115 ⟨true, b1, false, true, b4, true, false, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, b1, false, true, b4, true, false, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b5
                      · cases b4
                        · exact (f112 ⟨true, b1, true, true, false, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, true, true, false, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f88 ⟨true, b1, true, true, true, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, true, true, true, false, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b1
                          · exact (f17 ⟨true, false, true, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, true, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f45 ⟨true, true, true, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, true, true, false, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f49 ⟨true, b1, true, true, true, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, true, true, true, true, false, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · cases b5
                        · cases b4
                          · exact (f112 ⟨true, b1, true, true, false, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, true, true, false, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f88 ⟨true, b1, true, true, true, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, true, true, true, false, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f9 ⟨true, b1, true, true, b4, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g9 ⟨true, b1, true, true, b4, true, false, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b1
                        · cases b4
                          · cases b5
                            · exact (f112 ⟨true, false, true, true, false, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, true, true, false, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f26 ⟨true, false, true, true, false, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, true, false, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f88 ⟨true, false, true, true, true, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, false, true, true, true, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f72 ⟨true, false, true, true, true, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g72 ⟨true, false, true, true, true, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · cases b4
                            · exact (f112 ⟨true, true, true, true, false, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, true, true, false, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f88 ⟨true, true, true, true, true, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, true, true, true, true, false, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b4
                            · exact (f114 ⟨true, true, true, true, false, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g114 ⟨true, true, true, true, false, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f86 ⟨true, true, true, true, true, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g86 ⟨true, true, true, true, true, true, false, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                · cases b8
                  · cases b5
                    · cases b4
                      · exact (f112 ⟨true, b1, b2, true, false, false, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, b2, true, false, false, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f88 ⟨true, b1, b2, true, true, false, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, b2, true, true, false, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · cases b1
                        · exact (f17 ⟨true, false, b2, true, false, true, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, b2, true, false, true, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f45 ⟨true, true, b2, true, false, true, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, b2, true, false, true, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, b1, b2, true, true, true, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, b2, true, true, true, true, false, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b1
                    · cases b4
                      · cases b10
                        · cases b2
                          · cases b5
                            · exact (f112 ⟨true, false, false, true, false, false, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, false, true, false, false, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f115 ⟨true, false, false, true, false, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f112 ⟨true, false, true, true, false, false, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, true, true, false, false, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f36 ⟨true, false, true, true, false, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, false, true, true, false, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f112 ⟨true, false, b2, true, false, false, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, b2, true, false, false, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, false, false, true, false, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f26 ⟨true, false, true, true, false, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g26 ⟨true, false, true, true, false, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · cases b5
                          · exact (f88 ⟨true, false, false, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, false, false, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f115 ⟨true, false, false, true, true, true, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, true, true, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b5
                          · exact (f88 ⟨true, false, true, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, false, true, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b10
                            · exact (f36 ⟨true, false, true, true, true, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, false, true, true, true, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f72 ⟨true, false, true, true, true, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g72 ⟨true, false, true, true, true, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · cases b5
                        · cases b4
                          · exact (f112 ⟨true, true, false, true, false, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, false, true, false, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f88 ⟨true, true, false, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, true, false, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f115 ⟨true, true, false, true, b4, true, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, b4, true, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b5
                        · cases b4
                          · exact (f112 ⟨true, true, true, true, false, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, true, true, false, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f88 ⟨true, true, true, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, true, true, true, true, false, true, false, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b10
                          · exact (f36 ⟨true, true, true, true, b4, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g36 ⟨true, true, true, true, b4, true, true, false, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b4
                            · exact (f114 ⟨true, true, true, true, false, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g114 ⟨true, true, true, true, false, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f86 ⟨true, true, true, true, true, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g86 ⟨true, true, true, true, true, true, true, false, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
              · cases b5
                · cases b10
                  · cases b2
                    · exact (f121 ⟨true, b1, false, true, b4, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, b4, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f122 ⟨true, b1, true, true, b4, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, b4, false, b6, false, b8, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨true, b1, b2, true, b4, false, b6, false, b8, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, true, b4, false, b6, false, b8, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
                · exact (f59 ⟨true, b1, b2, true, b4, true, b6, false, b8, true, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, b4, true, b6, false, b8, true, b10, true, true, true⟩ rfl rfl).symm
    · cases b11
      · cases b10
        · cases b9
          · cases b0
            · cases b5
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f91 ⟨false, b1, false, b3, false, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, b1, false, b3, false, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f121 ⟨false, b1, false, b3, b4, false, b6, true, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨false, b1, false, b3, b4, false, b6, true, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f126 ⟨false, false, true, b3, b4, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f122 ⟨false, false, true, b3, b4, false, b6, true, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, false, true, b3, b4, false, b6, true, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f42 ⟨false, true, true, b3, b4, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f122 ⟨false, true, true, b3, b4, false, b6, true, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, true, true, b3, b4, false, b6, true, b8, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f54 ⟨false, b1, false, b3, false, true, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, b1, false, b3, false, true, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, true, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, true, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, b1, false, b3, b4, true, b6, true, b8, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨false, b1, false, b3, b4, true, b6, true, b8, false, false, false, true, true⟩ rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f126 ⟨false, false, true, b3, b4, true, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, true, b6, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, false, true, b3, b4, true, b6, true, b8, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, b6, true, b8, false, false, false, true, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b6
                      · exact (f29 ⟨false, true, true, b3, b4, true, false, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f11 ⟨false, true, true, b3, b4, true, true, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, true, b8, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, true, b3, b4, true, b6, true, b8, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, b6, true, b8, false, false, false, true, true⟩ rfl rfl).symm
            · cases b6
              · cases b8
                · cases b3
                  · cases b5
                    · cases b13
                      · exact (f47 ⟨true, b1, b2, false, b4, false, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g47 ⟨true, b1, b2, false, b4, false, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, false, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, false, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f81 ⟨true, b1, b2, false, b4, true, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g81 ⟨true, b1, b2, false, b4, true, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, b1, b2, false, b4, true, false, true, false, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, b4, true, false, true, false, false, false, false, true, true⟩ rfl rfl).symm
                  · cases b13
                    · exact (f6 ⟨true, b1, b2, true, b4, b5, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g6 ⟨true, b1, b2, true, b4, b5, false, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · cases b2
                        · exact (f121 ⟨true, b1, false, true, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, true, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, b4, false, false, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, b1, b2, true, b4, true, false, true, false, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, b4, true, false, true, false, false, false, false, true, true⟩ rfl rfl).symm
                · cases b4
                  · cases b13
                    · exact (f2 ⟨true, b1, b2, b3, false, b5, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g2 ⟨true, b1, b2, b3, false, b5, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · cases b2
                        · exact (f121 ⟨true, b1, false, b3, false, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, false, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, b3, false, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, false, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, b1, b2, b3, false, true, false, true, true, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, b3, false, true, false, true, true, false, false, false, true, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b5
                      · exact (f3 ⟨true, b1, b2, b3, true, false, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g3 ⟨true, b1, b2, b3, true, false, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f70 ⟨true, b1, b2, b3, true, true, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g70 ⟨true, b1, b2, b3, true, true, false, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · cases b2
                        · exact (f121 ⟨true, b1, false, b3, true, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, true, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, b3, true, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, true, false, false, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f59 ⟨true, b1, b2, b3, true, true, false, true, true, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, b3, true, true, false, true, true, false, false, false, true, true⟩ rfl rfl).symm
              · cases b5
                · cases b8
                  · cases b4
                    · cases b13
                      · exact (f110 ⟨true, b1, b2, b3, false, false, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, b1, b2, b3, false, false, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, b3, false, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, false, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, b3, false, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, false, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f102 ⟨true, b1, b2, b3, true, false, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, b1, b2, b3, true, false, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, b3, true, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, true, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, b3, true, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, true, false, true, true, false, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f113 ⟨true, b1, b2, b3, b4, false, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, b3, b4, false, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · exact (f121 ⟨true, b1, false, b3, b4, false, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, b4, false, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, b3, b4, false, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, b4, false, true, true, true, false, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b13
                  · cases b8
                    · cases b4
                      · exact (f110 ⟨true, b1, b2, b3, false, true, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g110 ⟨true, b1, b2, b3, false, true, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f102 ⟨true, b1, b2, b3, true, true, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g102 ⟨true, b1, b2, b3, true, true, true, true, false, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f113 ⟨true, b1, b2, b3, b4, true, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g113 ⟨true, b1, b2, b3, b4, true, true, true, true, false, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, b1, b2, b3, b4, true, true, true, b8, false, false, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, b3, b4, true, true, true, b8, false, false, false, true, true⟩ rfl rfl).symm
          · cases b0
            · cases b5
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f91 ⟨false, b1, false, b3, false, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, b1, false, b3, false, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f121 ⟨false, b1, false, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨false, b1, false, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f65 ⟨false, false, true, b3, b4, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f122 ⟨false, false, true, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, false, true, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f42 ⟨false, true, true, b3, b4, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f122 ⟨false, true, true, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, true, true, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f54 ⟨false, b1, false, b3, false, true, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, b1, false, b3, false, true, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, true, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, true, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, b1, false, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).trans (g59 ⟨false, b1, false, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f65 ⟨false, false, true, b3, b4, true, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, true, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, false, true, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b6
                      · exact (f29 ⟨false, true, true, b3, b4, true, false, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f11 ⟨false, true, true, b3, b4, true, true, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, true, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).symm
            · cases b13
              · cases b1
                · cases b5
                  · cases b4
                    · exact (f112 ⟨true, false, b2, b3, false, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, b2, b3, false, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f80 ⟨true, false, b2, b3, true, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, false, b2, b3, true, false, b6, true, b8, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b4
                      · exact (f16 ⟨true, false, b2, b3, false, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g16 ⟨true, false, b2, b3, false, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, false, b2, b3, true, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, false, b2, b3, true, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · cases b2
                        · exact (f115 ⟨true, false, false, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f98 ⟨true, false, true, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, false, true, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, false, false, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f50 ⟨true, false, true, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, false, true, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                · cases b8
                  · cases b5
                    · cases b4
                      · exact (f112 ⟨true, true, b2, b3, false, false, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, b2, b3, false, false, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f80 ⟨true, true, b2, b3, true, false, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, b2, b3, true, false, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · exact (f4 ⟨true, true, b2, b3, false, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, true, b2, b3, false, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, true, b2, b3, true, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, true, b2, b3, true, true, b6, true, false, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b3
                    · cases b5
                      · cases b4
                        · exact (f112 ⟨true, true, b2, false, false, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, b2, false, false, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f80 ⟨true, true, b2, false, true, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, b2, false, true, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, true, false, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f98 ⟨true, true, true, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g98 ⟨true, true, true, false, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b5
                      · cases b4
                        · exact (f112 ⟨true, true, b2, true, false, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, b2, true, false, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f80 ⟨true, true, b2, true, true, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, b2, true, true, false, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, true, false, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f50 ⟨true, true, true, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g50 ⟨true, true, true, true, b4, true, b6, true, true, true, false, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
              · cases b5
                · cases b2
                  · exact (f121 ⟨true, b1, false, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f122 ⟨true, b1, true, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, b4, false, b6, true, b8, true, false, false, true, true⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨true, b1, b2, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, b3, b4, true, b6, true, b8, true, false, false, true, true⟩ rfl rfl).symm
        · cases b9
          · cases b0
            · cases b5
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f91 ⟨false, b1, false, b3, false, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, b1, false, b3, false, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, b1, false, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, b1, false, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f85 ⟨false, false, true, b3, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨false, false, true, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, false, true, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f42 ⟨false, true, true, b3, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨false, true, true, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, true, true, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f54 ⟨false, b1, false, b3, false, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, b1, false, b3, false, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, b1, false, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).trans (g59 ⟨false, b1, false, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f85 ⟨false, false, true, b3, b4, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, false, true, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b6
                      · exact (f29 ⟨false, true, true, b3, b4, true, false, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f11 ⟨false, true, true, b3, b4, true, true, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, true, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).symm
            · cases b5
              · cases b13
                · cases b3
                  · exact (f87 ⟨true, b1, b2, false, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f75 ⟨true, b1, b2, true, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, b4, false, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f73 ⟨true, b1, b2, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, b3, b4, false, b6, true, b8, false, true, false, true, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · cases b3
                  · exact (f87 ⟨true, b1, b2, false, b4, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g87 ⟨true, b1, b2, false, b4, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f75 ⟨true, b1, b2, true, b4, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, b4, true, b6, true, b8, false, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨true, b1, b2, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, b3, b4, true, b6, true, b8, false, true, false, true, true⟩ rfl rfl).symm
          · cases b0
            · cases b5
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f91 ⟨false, b1, false, b3, false, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, b1, false, b3, false, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, b1, false, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, b1, false, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f85 ⟨false, false, true, b3, b4, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨false, false, true, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, false, true, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f42 ⟨false, true, true, b3, b4, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨false, true, true, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, true, true, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
              · cases b2
                · cases b13
                  · cases b4
                    · exact (f54 ⟨false, b1, false, b3, false, true, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, b1, false, b3, false, true, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f84 ⟨false, b1, false, b3, true, true, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g84 ⟨false, b1, false, b3, true, true, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨false, b1, false, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).trans (g59 ⟨false, b1, false, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).symm
                · cases b1
                  · cases b13
                    · exact (f85 ⟨false, false, true, b3, b4, true, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, true, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, false, true, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b6
                      · exact (f29 ⟨false, true, true, b3, b4, true, false, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f11 ⟨false, true, true, b3, b4, true, true, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨false, true, true, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).symm
            · cases b13
              · cases b1
                · cases b5
                  · cases b4
                    · exact (f112 ⟨true, false, b2, b3, false, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, b2, b3, false, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f80 ⟨true, false, b2, b3, true, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, false, b2, b3, true, false, b6, true, b8, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b8
                    · cases b4
                      · exact (f16 ⟨true, false, b2, b3, false, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g16 ⟨true, false, b2, b3, false, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, false, b2, b3, true, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, false, b2, b3, true, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b6
                      · cases b3
                        · cases b2
                          · exact (f115 ⟨true, false, false, false, b4, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, false, b4, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · cases b4
                            · exact (f120 ⟨true, false, true, false, false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g120 ⟨true, false, true, false, false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f117 ⟨true, false, true, false, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g117 ⟨true, false, true, false, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · cases b2
                            · exact (f115 ⟨true, false, false, true, false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f120 ⟨true, false, true, true, false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g120 ⟨true, false, true, true, false, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, false, false, true, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, true, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f89 ⟨true, false, true, true, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g89 ⟨true, false, true, true, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, false, false, b3, b4, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, b4, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · cases b4
                          · exact (f120 ⟨true, false, true, b3, false, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g120 ⟨true, false, true, b3, false, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f51 ⟨true, false, true, b3, true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, false, true, b3, true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                · cases b8
                  · cases b5
                    · cases b4
                      · exact (f112 ⟨true, true, b2, b3, false, false, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, b2, b3, false, false, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f80 ⟨true, true, b2, b3, true, false, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, b2, b3, true, false, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · exact (f4 ⟨true, true, b2, b3, false, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g4 ⟨true, true, b2, b3, false, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, true, b2, b3, true, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, true, b2, b3, true, true, b6, true, false, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b2
                    · cases b5
                      · cases b4
                        · exact (f112 ⟨true, true, false, b3, false, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, false, b3, false, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f80 ⟨true, true, false, b3, true, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, false, b3, true, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f115 ⟨true, true, false, b3, b4, true, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, b4, true, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b3
                      · cases b4
                        · cases b5
                          · exact (f112 ⟨true, true, true, false, false, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, true, false, false, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f120 ⟨true, true, true, false, false, true, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g120 ⟨true, true, true, false, false, true, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b6
                          · cases b5
                            · exact (f80 ⟨true, true, true, false, true, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, true, false, true, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f18 ⟨true, true, true, false, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g18 ⟨true, true, true, false, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f80 ⟨true, true, true, false, true, false, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, true, false, true, false, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f51 ⟨true, true, true, false, true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, true, true, false, true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b4
                        · cases b5
                          · exact (f112 ⟨true, true, true, true, false, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, true, true, false, false, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f120 ⟨true, true, true, true, false, true, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g120 ⟨true, true, true, true, false, true, b6, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b6
                          · cases b5
                            · exact (f80 ⟨true, true, true, true, true, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, true, true, true, false, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f38 ⟨true, true, true, true, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g38 ⟨true, true, true, true, true, true, false, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b5
                            · exact (f80 ⟨true, true, true, true, true, false, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g80 ⟨true, true, true, true, true, false, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f51 ⟨true, true, true, true, true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g51 ⟨true, true, true, true, true, true, true, true, true, true, true, false, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
              · cases b5
                · exact (f73 ⟨true, b1, b2, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, b3, b4, false, b6, true, b8, true, true, false, true, true⟩ rfl rfl rfl rfl).symm
                · exact (f59 ⟨true, b1, b2, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, b3, b4, true, b6, true, b8, true, true, false, true, true⟩ rfl rfl).symm
      · cases b0
        · cases b5
          · cases b2
            · cases b13
              · cases b4
                · exact (f91 ⟨false, b1, false, b3, false, false, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g91 ⟨false, b1, false, b3, false, false, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · exact (f66 ⟨false, b1, false, b3, true, false, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, b1, false, b3, true, false, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
              · cases b10
                · exact (f121 ⟨false, b1, false, b3, b4, false, b6, true, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨false, b1, false, b3, b4, false, b6, true, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                · exact (f73 ⟨false, b1, false, b3, b4, false, b6, true, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, b1, false, b3, b4, false, b6, true, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).symm
            · cases b1
              · cases b10
                · cases b13
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, false, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, false, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, false, b6, true, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, false, b6, true, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f122 ⟨false, false, true, b3, b4, false, b6, true, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, false, true, b3, b4, false, b6, true, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f85 ⟨false, false, true, b3, b4, false, b6, true, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, false, b6, true, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, false, true, b3, b4, false, b6, true, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, false, true, b3, b4, false, b6, true, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · exact (f42 ⟨false, true, true, b3, b4, false, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g42 ⟨false, true, true, b3, b4, false, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · cases b10
                  · exact (f122 ⟨false, true, true, b3, b4, false, b6, true, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨false, true, true, b3, b4, false, b6, true, b8, b9, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨false, true, true, b3, b4, false, b6, true, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨false, true, true, b3, b4, false, b6, true, b8, b9, true, true, true, true⟩ rfl rfl rfl rfl).symm
          · cases b2
            · cases b13
              · cases b4
                · exact (f54 ⟨false, b1, false, b3, false, true, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g54 ⟨false, b1, false, b3, false, true, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · exact (f66 ⟨false, b1, false, b3, true, true, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g66 ⟨false, b1, false, b3, true, true, b6, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl).symm
              · exact (f59 ⟨false, b1, false, b3, b4, true, b6, true, b8, b9, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨false, b1, false, b3, b4, true, b6, true, b8, b9, b10, true, true, true⟩ rfl rfl).symm
            · cases b1
              · cases b13
                · cases b10
                  · cases b9
                    · exact (f126 ⟨false, false, true, b3, b4, true, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g126 ⟨false, false, true, b3, b4, true, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f65 ⟨false, false, true, b3, b4, true, b6, true, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g65 ⟨false, false, true, b3, b4, true, b6, true, b8, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f85 ⟨false, false, true, b3, b4, true, b6, true, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g85 ⟨false, false, true, b3, b4, true, b6, true, b8, b9, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, false, true, b3, b4, true, b6, true, b8, b9, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨false, false, true, b3, b4, true, b6, true, b8, b9, b10, true, true, true⟩ rfl rfl).symm
              · cases b13
                · cases b6
                  · exact (f29 ⟨false, true, true, b3, b4, true, false, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g29 ⟨false, true, true, b3, b4, true, false, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · exact (f11 ⟨false, true, true, b3, b4, true, true, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g11 ⟨false, true, true, b3, b4, true, true, true, b8, b9, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨false, true, true, b3, b4, true, b6, true, b8, b9, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨false, true, true, b3, b4, true, b6, true, b8, b9, b10, true, true, true⟩ rfl rfl).symm
        · cases b9
          · cases b3
            · cases b4
              · cases b10
                · cases b5
                  · cases b6
                    · cases b13
                      · cases b2
                        · exact (f25 ⟨true, b1, false, false, false, false, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g25 ⟨true, b1, false, false, false, false, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f116 ⟨true, b1, true, false, false, false, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g116 ⟨true, b1, true, false, false, false, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, false, false, false, false, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, false, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, false, false, false, false, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, false, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f43 ⟨true, b1, b2, false, false, false, true, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, b1, b2, false, false, false, true, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, b1, false, false, false, false, true, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, false, false, true, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, b1, true, false, false, false, true, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, false, false, true, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b6
                      · cases b2
                        · cases b1
                          · exact (f57 ⟨true, false, false, false, false, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g57 ⟨true, false, false, false, false, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b8
                            · exact (f22 ⟨true, true, false, false, false, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g22 ⟨true, true, false, false, false, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f97 ⟨true, true, false, false, false, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g97 ⟨true, true, false, false, false, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f19 ⟨true, b1, true, false, false, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, b1, true, false, false, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f43 ⟨true, b1, b2, false, false, true, true, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, b1, b2, false, false, true, true, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, false, false, true, b6, true, b8, false, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, false, true, b6, true, b8, false, false, true, true, true⟩ rfl rfl).symm
                · cases b5
                  · cases b13
                    · exact (f61 ⟨true, b1, b2, false, false, false, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, false, false, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨true, b1, b2, false, false, false, b6, true, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, false, false, false, b6, true, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f61 ⟨true, b1, b2, false, false, true, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, false, true, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, false, false, true, b6, true, b8, false, true, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, false, true, b6, true, b8, false, true, true, true, true⟩ rfl rfl).symm
              · cases b13
                · cases b6
                  · cases b10
                    · cases b5
                      · exact (f8 ⟨true, b1, b2, false, true, false, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g8 ⟨true, b1, b2, false, true, false, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b1
                        · cases b2
                          · exact (f13 ⟨true, false, false, false, true, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g13 ⟨true, false, false, false, true, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f19 ⟨true, false, true, false, true, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, false, true, false, true, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b2
                          · cases b8
                            · exact (f31 ⟨true, true, false, false, true, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g31 ⟨true, true, false, false, true, true, false, true, false, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                            · exact (f23 ⟨true, true, false, false, true, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g23 ⟨true, true, false, false, true, true, false, true, true, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · exact (f19 ⟨true, true, true, false, true, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g19 ⟨true, true, true, false, true, true, false, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f61 ⟨true, b1, b2, false, true, b5, false, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, true, b5, false, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                  · cases b10
                    · exact (f43 ⟨true, b1, b2, false, true, b5, true, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g43 ⟨true, b1, b2, false, true, b5, true, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f61 ⟨true, b1, b2, false, true, b5, true, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g61 ⟨true, b1, b2, false, true, b5, true, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                · cases b5
                  · cases b10
                    · cases b2
                      · exact (f121 ⟨true, b1, false, false, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, false, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, false, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, false, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨true, b1, b2, false, true, false, b6, true, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, false, true, false, b6, true, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, b1, b2, false, true, true, b6, true, b8, false, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, false, true, true, b6, true, b8, false, b10, true, true, true⟩ rfl rfl).symm
            · cases b10
              · cases b4
                · cases b5
                  · cases b13
                    · exact (f74 ⟨true, b1, b2, true, false, false, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, b1, b2, true, false, false, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · exact (f121 ⟨true, b1, false, true, false, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, false, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, true, false, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, false, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f94 ⟨true, b1, b2, true, false, true, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g94 ⟨true, b1, b2, true, false, true, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, true, false, true, b6, true, b8, false, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, false, true, b6, true, b8, false, false, true, true, true⟩ rfl rfl).symm
                · cases b13
                  · cases b5
                    · exact (f74 ⟨true, b1, b2, true, true, false, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g74 ⟨true, b1, b2, true, true, false, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f52 ⟨true, b1, b2, true, true, true, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).trans (g52 ⟨true, b1, b2, true, true, true, b6, true, b8, false, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b5
                    · cases b2
                      · exact (f121 ⟨true, b1, false, true, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, true, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, true, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, true, true, false, b6, true, b8, false, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, b1, b2, true, true, true, b6, true, b8, false, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, true, true, b6, true, b8, false, false, true, true, true⟩ rfl rfl).symm
              · cases b5
                · cases b13
                  · exact (f75 ⟨true, b1, b2, true, b4, false, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, b4, false, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨true, b1, b2, true, b4, false, b6, true, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, true, b4, false, b6, true, b8, false, true, true, true, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · exact (f75 ⟨true, b1, b2, true, b4, true, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).trans (g75 ⟨true, b1, b2, true, b4, true, b6, true, b8, false, true, true, true, false⟩ rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, b1, b2, true, b4, true, b6, true, b8, false, true, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, true, b4, true, b6, true, b8, false, true, true, true, true⟩ rfl rfl).symm
          · cases b8
            · cases b5
              · cases b10
                · cases b4
                  · cases b13
                    · exact (f112 ⟨true, b1, b2, b3, false, false, b6, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, b2, b3, false, false, b6, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · exact (f121 ⟨true, b1, false, b3, false, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, false, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, b3, false, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, false, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · exact (f88 ⟨true, b1, b2, b3, true, false, b6, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, b2, b3, true, false, b6, true, false, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b2
                      · exact (f121 ⟨true, b1, false, b3, true, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, b1, false, b3, true, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                      · exact (f122 ⟨true, b1, true, b3, true, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, b1, true, b3, true, false, b6, true, false, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                · cases b13
                  · cases b4
                    · exact (f112 ⟨true, b1, b2, b3, false, false, b6, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, b1, b2, b3, false, false, b6, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · exact (f88 ⟨true, b1, b2, b3, true, false, b6, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, b1, b2, b3, true, false, b6, true, false, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · exact (f73 ⟨true, b1, b2, b3, b4, false, b6, true, false, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, b1, b2, b3, b4, false, b6, true, false, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
              · cases b13
                · cases b3
                  · cases b1
                    · cases b4
                      · cases b2
                        · exact (f103 ⟨true, false, false, false, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g103 ⟨true, false, false, false, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · exact (f100 ⟨true, false, true, false, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g100 ⟨true, false, true, false, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, false, b2, false, true, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, false, b2, false, true, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · cases b4
                      · exact (f40 ⟨true, true, b2, false, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g40 ⟨true, true, b2, false, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f49 ⟨true, true, b2, false, true, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, true, b2, false, true, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                  · cases b4
                    · cases b1
                      · exact (f17 ⟨true, false, b2, true, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g17 ⟨true, false, b2, true, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f45 ⟨true, true, b2, true, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g45 ⟨true, true, b2, true, false, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f49 ⟨true, b1, b2, true, true, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g49 ⟨true, b1, b2, true, true, true, b6, true, false, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                · exact (f59 ⟨true, b1, b2, b3, b4, true, b6, true, false, true, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨true, b1, b2, b3, b4, true, b6, true, false, true, b10, true, true, true⟩ rfl rfl).symm
            · cases b1
              · cases b5
                · cases b10
                  · cases b4
                    · cases b13
                      · exact (f112 ⟨true, false, b2, b3, false, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, b2, b3, false, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, false, false, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, false, false, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, false, true, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, false, true, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f88 ⟨true, false, b2, b3, true, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, false, b2, b3, true, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, false, false, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, false, false, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, false, true, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, false, true, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b4
                      · exact (f112 ⟨true, false, b2, b3, false, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, false, b2, b3, false, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f88 ⟨true, false, b2, b3, true, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, false, b2, b3, true, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨true, false, b2, b3, b4, false, b6, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, false, b2, b3, b4, false, b6, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
                · cases b13
                  · cases b2
                    · exact (f115 ⟨true, false, false, b3, b4, true, b6, true, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, false, false, b3, b4, true, b6, true, true, true, b10, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                    · cases b10
                      · exact (f108 ⟨true, false, true, b3, b4, true, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g108 ⟨true, false, true, b3, b4, true, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · exact (f125 ⟨true, false, true, b3, b4, true, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, false, true, b3, b4, true, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                  · exact (f59 ⟨true, false, b2, b3, b4, true, b6, true, true, true, b10, true, true, true⟩ rfl rfl).trans (g59 ⟨true, false, b2, b3, b4, true, b6, true, true, true, b10, true, true, true⟩ rfl rfl).symm
              · cases b5
                · cases b10
                  · cases b4
                    · cases b13
                      · exact (f112 ⟨true, true, b2, b3, false, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, b2, b3, false, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, true, false, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, true, false, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, true, true, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, true, true, b3, false, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                    · cases b13
                      · exact (f88 ⟨true, true, b2, b3, true, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, true, b2, b3, true, false, b6, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f121 ⟨true, true, false, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g121 ⟨true, true, false, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                        · exact (f122 ⟨true, true, true, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).trans (g122 ⟨true, true, true, b3, true, false, b6, true, true, true, false, true, true, true⟩ rfl rfl rfl rfl rfl).symm
                  · cases b13
                    · cases b4
                      · exact (f112 ⟨true, true, b2, b3, false, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g112 ⟨true, true, b2, b3, false, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f88 ⟨true, true, b2, b3, true, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).trans (g88 ⟨true, true, b2, b3, true, false, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f73 ⟨true, true, b2, b3, b4, false, b6, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).trans (g73 ⟨true, true, b2, b3, b4, false, b6, true, true, true, true, true, true, true⟩ rfl rfl rfl rfl).symm
                · cases b10
                  · cases b13
                    · cases b6
                      · cases b4
                        · cases b2
                          · exact (f115 ⟨true, true, false, b3, false, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, false, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                          · exact (f118 ⟨true, true, true, b3, false, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g118 ⟨true, true, true, b3, false, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                        · cases b3
                          · cases b2
                            · exact (f115 ⟨true, true, false, false, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, false, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f124 ⟨true, true, true, false, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g124 ⟨true, true, true, false, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                          · cases b2
                            · exact (f115 ⟨true, true, false, true, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, true, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                            · exact (f109 ⟨true, true, true, true, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g109 ⟨true, true, true, true, true, true, false, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                      · cases b2
                        · exact (f115 ⟨true, true, false, b3, b4, true, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, b4, true, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                        · exact (f24 ⟨true, true, true, b3, b4, true, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g24 ⟨true, true, true, b3, b4, true, true, true, true, true, false, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, b4, true, b6, true, true, true, false, true, true, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, b4, true, b6, true, true, true, false, true, true, true⟩ rfl rfl).symm
                  · cases b13
                    · cases b2
                      · exact (f115 ⟨true, true, false, b3, b4, true, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).trans (g115 ⟨true, true, false, b3, b4, true, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl).symm
                      · exact (f125 ⟨true, true, true, b3, b4, true, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).trans (g125 ⟨true, true, true, b3, b4, true, b6, true, true, true, true, true, true, false⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl).symm
                    · exact (f59 ⟨true, true, b2, b3, b4, true, b6, true, true, true, true, true, true, true⟩ rfl rfl).trans (g59 ⟨true, true, b2, b3, b4, true, b6, true, true, true, true, true, true, true⟩ rfl rfl).symm

end TblComplete
