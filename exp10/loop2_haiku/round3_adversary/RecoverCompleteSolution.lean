import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

theorem passes_ref (f : Decide) (hf : Passes f) (c : Case) : f c = ref c := by
  obtain ⟨h1, h2, h3, h4, h5, _, h7, h8⟩ := hf
  cases hk : c.pidKnown
  · cases ha : c.age with
    | none => rw [h7 c hk ha]; simp [ref, hk, ha]
    | some a =>
      rcases Nat.lt_trichotomy a c.staleAfter with h | h | h
      · rw [h5 c a hk ha h]; simp [ref, hk, ha]; omega
      · rw [h8 c a hk ha h]; simp [ref, hk, ha]; omega
      · rw [h4 c a hk ha h]; simp [ref, hk, ha]; omega
  · cases hal : c.alive
    · rw [h1 c hk hal]; simp [ref, hk, hal]
    · cases hr : c.reused
      · rw [h3 c hk hal hr]; simp [ref, hk, hal, hr]
      · rw [h2 c hk hr]; simp [ref, hk, hal, hr]

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  rw [passes_ref f hf c, passes_ref g hg c]

end RecoverComplete
