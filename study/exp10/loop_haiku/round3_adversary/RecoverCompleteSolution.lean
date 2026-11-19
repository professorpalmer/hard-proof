import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f1, f2, f3, _, f5, _, f7, f8⟩ := hf
  obtain ⟨g1, g2, g3, _, g5, _, g7, g8⟩ := hg
  obtain ⟨pk, al, ru, ag, sa⟩ := c
  cases pk
  · cases ag with
    | none => rw [f8 _ rfl rfl, g8 _ rfl rfl]
    | some a =>
      by_cases h : sa ≤ a
      · rw [f7 _ a rfl rfl h, g7 _ a rfl rfl h]
      · have h' : a < sa := by omega
        rw [f5 _ a rfl rfl h', g5 _ a rfl rfl h']
  · cases al
    · rw [f1 _ rfl rfl, g1 _ rfl rfl]
    · cases ru
      · rw [f3 _ rfl rfl rfl, g3 _ rfl rfl rfl]
      · rw [f2 _ rfl rfl, g2 _ rfl rfl]

end RecoverComplete
