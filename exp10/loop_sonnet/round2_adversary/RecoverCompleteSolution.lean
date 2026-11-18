import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f1, f2, f3, f4, _, f6, f7⟩ := hf
  obtain ⟨g1, g2, g3, g4, _, g6, g7⟩ := hg
  cases hp : c.pidKnown
  · cases hage : c.age with
    | none => rw [f7 c hp hage, g7 c hp hage]
    | some a =>
      by_cases h : a ≥ c.staleAfter
      · rw [f4 c hp a hage h, g4 c hp a hage h]
      · have h' : a < c.staleAfter := by omega
        rw [f6 c hp a hage h', g6 c hp a hage h']
  · cases ha : c.alive
    · rw [f1 c hp ha, g1 c hp ha]
    · cases hr : c.reused
      · rw [f3 c hp ha hr, g3 c hp ha hr]
      · rw [f2 c hp hr, g2 c hp hr]

end RecoverComplete
