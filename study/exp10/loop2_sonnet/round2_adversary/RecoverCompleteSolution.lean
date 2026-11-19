import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

theorem eq_ref (f : Decide) (h : Passes f) (c : Case) : f c = ref c := by
  obtain ⟨h1, h2, h3, h4, _, h6, h7⟩ := h
  obtain ⟨pk, al, re, ag, st⟩ := c
  cases pk
  · cases ag with
    | none => simpa [ref] using h7 ⟨false, al, re, none, st⟩ rfl rfl
    | some a =>
      by_cases hg : a ≥ st
      · have := h4 ⟨false, al, re, some a, st⟩ rfl a rfl hg
        simp [ref, hg] at *; exact this
      · have := h6 ⟨false, al, re, some a, st⟩ rfl a rfl (show a < st by omega)
        simp [ref, hg] at *; exact this
  · cases al
    · have := h1 ⟨true, false, re, ag, st⟩ rfl rfl
      simp [ref] at *; exact this
    · cases re
      · have := h3 ⟨true, true, false, ag, st⟩ rfl rfl rfl
        simp [ref] at *; exact this
      · have := h2 ⟨true, true, true, ag, st⟩ rfl rfl
        simp [ref] at *; exact this

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  rw [eq_ref f hf c, eq_ref g hg c]

end RecoverComplete
