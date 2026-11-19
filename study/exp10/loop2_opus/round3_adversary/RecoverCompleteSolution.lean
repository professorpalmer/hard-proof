import Recover
import RecoverLaws

open Recover

namespace RecoverComplete

theorem eq_ref (f : Decide) (h : Passes f) (c : Case) : f c = ref c := by
  obtain ⟨hd, hr, hl, _, hf, _, hn, hge⟩ := h
  obtain ⟨pk, al, ru, age, s⟩ := c
  cases pk
  · cases age with
    | none => simpa [ref] using hn _ rfl rfl
    | some a =>
      by_cases hc : a ≥ s
      · have := hge ⟨false, al, ru, some a, s⟩ a rfl rfl hc
        simp [ref, this, hc]
      · have := hf ⟨false, al, ru, some a, s⟩ a rfl rfl (show a < s by omega)
        simp [ref, this, hc]
  · cases al
    · have := hd ⟨true, false, ru, age, s⟩ rfl rfl
      simp [ref, this]
    · cases ru
      · have := hl ⟨true, true, false, age, s⟩ rfl rfl rfl
        simp [ref, this]
      · have := hr ⟨true, true, true, age, s⟩ rfl rfl
        simp [ref, this]

theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  rw [eq_ref f hf c, eq_ref g hg c]

end RecoverComplete
