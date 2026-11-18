/-
hardproof domain `clamp`. AUTHOR FILE (pinned).

One law for each sentence of `DESCRIPTION.md`.
-/
import Types

namespace HP

/-- Sentence 1: the result is in the closed range from lo to hi. -/
def InRange (f : Impl) : Prop :=
  ∀ i : Input, Legal i → i.lo ≤ f i ∧ f i ≤ i.hi

/-- Sentence 2: when x is less than lo, the result is lo. -/
def BelowGivesLo (f : Impl) : Prop :=
  ∀ i : Input, Legal i → i.x < i.lo → f i = i.lo

/-- Sentence 3: when x is more than hi, the result is hi. -/
def AboveGivesHi (f : Impl) : Prop :=
  ∀ i : Input, Legal i → i.hi < i.x → f i = i.hi

/-- Sentence 4: else the result is x. -/
def InsideGivesX (f : Impl) : Prop :=
  ∀ i : Input, Legal i → i.lo ≤ i.x → i.x ≤ i.hi → f i = i.x

def Passes (f : Impl) : Prop :=
  InRange f ∧ BelowGivesLo f ∧ AboveGivesHi f ∧ InsideGivesX f

theorem some_design_fails : ∃ f : Impl, ¬ Passes f := by
  refine ⟨fun _ => 0, ?_⟩
  intro h
  have := h.2.1 ⟨0, 1, 1⟩ rfl (by decide)
  simp at this

end HP
