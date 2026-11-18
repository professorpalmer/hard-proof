import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19,
    F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31⟩ := hf
  obtain ⟨G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, G18, G19,
    G20, G21, G22, G23, G24, G25, G26, G27, G28, G29, G30, G31⟩ := hg
  cases h2 : c.b2
  · cases h1 : c.b1
    · cases h3 : c.b3
      · cases h9 : c.b9
        · cases h6 : c.b6
          · cases h7 : c.b7
            · rw [F0 c h2 h1 h3 h9 h6 h7, G0 c h2 h1 h3 h9 h6 h7]
            · cases h0 : c.b0
              · rw [F1 c h2 h1 h3 h9 h6 h7 h0, G1 c h2 h1 h3 h9 h6 h7 h0]
              · rw [F2 c h2 h1 h3 h9 h6 h7 h0, G2 c h2 h1 h3 h9 h6 h7 h0]
          · rw [F3 c h2 h1 h3 h9 h6, G3 c h2 h1 h3 h9 h6]
        · cases h0 : c.b0
          · cases h7 : c.b7
            · cases h5 : c.b5
              · rw [F4 c h2 h1 h3 h9 h0 h7 h5, G4 c h2 h1 h3 h9 h0 h7 h5]
              · rw [F5 c h2 h1 h3 h9 h0 h7 h5, G5 c h2 h1 h3 h9 h0 h7 h5]
            · rw [F6 c h2 h1 h3 h9 h0 h7, G6 c h2 h1 h3 h9 h0 h7]
          · rw [F7 c h2 h1 h3 h9 h0, G7 c h2 h1 h3 h9 h0]
      · rw [F8 c h2 h1 h3, G8 c h2 h1 h3]
    · cases h0 : c.b0
      · cases h8 : c.b8
        · cases h6 : c.b6
          · rw [F9 c h2 h1 h0 h8 h6, G9 c h2 h1 h0 h8 h6]
          · rw [F10 c h2 h1 h0 h8 h6, G10 c h2 h1 h0 h8 h6]
        · cases h6 : c.b6
          · cases h9 : c.b9
            · rw [F11 c h2 h1 h0 h8 h6 h9, G11 c h2 h1 h0 h8 h6 h9]
            · cases h4 : c.b4
              · cases h5 : c.b5
                · rw [F12 c h2 h1 h0 h8 h6 h9 h4 h5, G12 c h2 h1 h0 h8 h6 h9 h4 h5]
                · rw [F13 c h2 h1 h0 h8 h6 h9 h4 h5, G13 c h2 h1 h0 h8 h6 h9 h4 h5]
              · rw [F14 c h2 h1 h0 h8 h6 h9 h4, G14 c h2 h1 h0 h8 h6 h9 h4]
          · rw [F15 c h2 h1 h0 h8 h6, G15 c h2 h1 h0 h8 h6]
      · cases h3 : c.b3
        · rw [F16 c h2 h1 h0 h3, G16 c h2 h1 h0 h3]
        · cases h9 : c.b9
          · rw [F17 c h2 h1 h0 h3 h9, G17 c h2 h1 h0 h3 h9]
          · rw [F18 c h2 h1 h0 h3 h9, G18 c h2 h1 h0 h3 h9]
  · cases h6 : c.b6
    · cases h8 : c.b8
      · cases h9 : c.b9
        · cases h3 : c.b3
          · cases h7 : c.b7
            · rw [F19 c h2 h6 h8 h9 h3 h7, G19 c h2 h6 h8 h9 h3 h7]
            · rw [F20 c h2 h6 h8 h9 h3 h7, G20 c h2 h6 h8 h9 h3 h7]
          · cases h7 : c.b7
            · rw [F21 c h2 h6 h8 h9 h3 h7, G21 c h2 h6 h8 h9 h3 h7]
            · rw [F22 c h2 h6 h8 h9 h3 h7, G22 c h2 h6 h8 h9 h3 h7]
        · cases h4 : c.b4
          · cases h5 : c.b5
            · rw [F23 c h2 h6 h8 h9 h4 h5, G23 c h2 h6 h8 h9 h4 h5]
            · rw [F24 c h2 h6 h8 h9 h4 h5, G24 c h2 h6 h8 h9 h4 h5]
          · cases h7 : c.b7
            · cases h0 : c.b0
              · rw [F25 c h2 h6 h8 h9 h4 h7 h0, G25 c h2 h6 h8 h9 h4 h7 h0]
              · rw [F26 c h2 h6 h8 h9 h4 h7 h0, G26 c h2 h6 h8 h9 h4 h7 h0]
            · rw [F27 c h2 h6 h8 h9 h4 h7, G27 c h2 h6 h8 h9 h4 h7]
      · cases h5 : c.b5
        · cases h3 : c.b3
          · rw [F28 c h2 h6 h8 h5 h3, G28 c h2 h6 h8 h5 h3]
          · rw [F29 c h2 h6 h8 h5 h3, G29 c h2 h6 h8 h5 h3]
        · rw [F30 c h2 h6 h8 h5, G30 c h2 h6 h8 h5]
    · rw [F31 c h2 h6, G31 c h2 h6]

end TblComplete
