import Tbl
import TblLaws

open Tbl

namespace TblComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19,f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31⟩ := hf
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18,g19,g20,g21,g22,g23,g24,g25,g26,g27,g28,g29,g30,g31⟩ := hg
  cases h2 : c.b2
  · cases h1 : c.b1
    · cases h3 : c.b3
      · cases h9 : c.b9
        · cases h6 : c.b6
          · cases h7 : c.b7
            · simp only [f0 c, g0 c, *]
            · cases h0 : c.b0
              · simp only [f1 c, g1 c, *]
              · simp only [f2 c, g2 c, *]
          · simp only [f3 c, g3 c, *]
        · cases h0 : c.b0
          · cases h7 : c.b7
            · cases h5 : c.b5
              · simp only [f4 c, g4 c, *]
              · simp only [f5 c, g5 c, *]
            · simp only [f6 c, g6 c, *]
          · simp only [f7 c, g7 c, *]
      · simp only [f8 c, g8 c, *]
    · cases h0 : c.b0
      · cases h8 : c.b8
        · cases h6 : c.b6
          · simp only [f9 c, g9 c, *]
          · simp only [f10 c, g10 c, *]
        · cases h6 : c.b6
          · cases h9 : c.b9
            · simp only [f11 c, g11 c, *]
            · cases h4 : c.b4
              · cases h5 : c.b5
                · simp only [f12 c, g12 c, *]
                · simp only [f13 c, g13 c, *]
              · simp only [f14 c, g14 c, *]
          · simp only [f15 c, g15 c, *]
      · cases h3 : c.b3
        · simp only [f16 c, g16 c, *]
        · cases h9 : c.b9
          · simp only [f17 c, g17 c, *]
          · simp only [f18 c, g18 c, *]
  · cases h6 : c.b6
    · cases h8 : c.b8
      · cases h9 : c.b9
        · cases h3 : c.b3
          · cases h7 : c.b7
            · simp only [f19 c, g19 c, *]
            · simp only [f20 c, g20 c, *]
          · cases h7 : c.b7
            · simp only [f21 c, g21 c, *]
            · simp only [f22 c, g22 c, *]
        · cases h4 : c.b4
          · cases h5 : c.b5
            · simp only [f23 c, g23 c, *]
            · simp only [f24 c, g24 c, *]
          · cases h7 : c.b7
            · cases h0 : c.b0
              · simp only [f25 c, g25 c, *]
              · simp only [f26 c, g26 c, *]
            · simp only [f27 c, g27 c, *]
      · cases h5 : c.b5
        · cases h3 : c.b3
          · simp only [f28 c, g28 c, *]
          · simp only [f29 c, g29 c, *]
        · simp only [f30 c, g30 c, *]
    · simp only [f31 c, g31 c, *]

end TblComplete
