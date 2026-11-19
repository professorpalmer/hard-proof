import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

theorem eq_ref (f : Decide) (h : Passes f) (c : Case) : f c = ref c := by
  obtain ⟨h1, h2, h3, h4, h5, _, h7, h8⟩ := h
  obtain ⟨pk, al, ru, ag, st⟩ := c
  cases pk
  · cases ag with
    | none => simpa [ref] using h7 _ rfl rfl
    | some a =>
      by_cases hge : a ≥ st
      · have := h8 ⟨false, al, ru, some a, st⟩ a rfl rfl hge
        simp [ref, hge, this]
      · have hlt : a < st := by omega
        have := h5 ⟨false, al, ru, some a, st⟩ a rfl rfl hlt
        simp [ref, hge, this]
  · cases al
    · have := h1 ⟨true, false, ru, ag, st⟩ rfl rfl
      simp [ref, this]
    · cases ru
      · have := h3 ⟨true, true, false, ag, st⟩ rfl rfl rfl
        simp [ref, this]
      · have := h2 ⟨true, true, true, ag, st⟩ rfl rfl
        simp [ref, this]

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  rw [eq_ref f hf c, eq_ref g hg c]

end RecoverComplete
