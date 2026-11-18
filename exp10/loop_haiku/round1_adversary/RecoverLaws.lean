import Recover

/-!
Laws for the stale-lock recovery rule, written from `DESCRIPTION.md` only.

Each law is one requirement of the description. A law names the sentence it
comes from. Where the description is silent or unclear, there is no law (see
the report for the list).
-/

namespace Recover

/-- Sentence 1: "A later process recovers an orphan whose owner PID is no longer
alive". A known owner pid that is not alive means the lock file must be removed. -/
def PidDeadRemoved (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.alive = false → f c = true

/-- Sentence 3: "The owner is gone when its pid is dead or now names a later
process", with sentence 1 ("recovers an orphan"). A known owner pid that now names
a later process means the owner is gone, so the lock file must be removed. -/
def PidReusedRemoved (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.reused = true → f c = true

/-- Sentence 3: "Remove only an orphaned lock". A known owner pid that is alive
and not reused means the owner is not gone, so the lock file must be kept. -/
def LiveOwnerKept (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.alive = true → c.reused = false → f c = false

/-- Sentence 1: "malformed/unknown owners are recovered after `stale_after`
seconds". An owner with no valid pid, whose known age is more than `stale_after`,
must be removed. -/
def UnknownOlderRemoved (f : Decide) : Prop :=
  ∀ (c : Case) (a : Nat), c.pidKnown = false → c.age = some a →
    c.staleAfter < a → f c = true

/-- Sentence 1: "malformed/unknown owners are recovered after `stale_after`
seconds". An owner with no valid pid, whose known age is less than `stale_after`,
is not yet recovered, so the lock file must be kept. -/
def UnknownYoungerKept (f : Decide) : Prop :=
  ∀ (c : Case) (a : Nat), c.pidKnown = false → c.age = some a →
    a < c.staleAfter → f c = false

/-- Sentence 2: "`stale_after` is only used when an owner cannot be identified
safely". When the owner pid is known, the decision does not depend on the age or
on `stale_after`. -/
def StaleAfterOnlyUnknown (f : Decide) : Prop :=
  ∀ (c : Case), c.pidKnown = true → ∀ (a : Option Nat) (s : Nat),
    f c = f { c with age := a, staleAfter := s }

/-- The conjunction of the laws above. -/
def Passes (f : Decide) : Prop :=
  PidDeadRemoved f ∧ PidReusedRemoved f ∧ LiveOwnerKept f ∧
  UnknownOlderRemoved f ∧ UnknownYoungerKept f ∧ StaleAfterOnlyUnknown f

theorem ref_passes : Passes ref := by
  unfold Passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hk hd
    simp [ref, hk, hd]
  · intro c hk hr
    simp [ref, hk, hr]
  · intro c hk ha hr
    simp [ref, hk, ha, hr]
  · intro c a hk ha hlt
    simp [ref, hk, ha] <;> omega
  · intro c a hk ha hlt
    simp [ref, hk, ha] <;> omega
  · intro c hk a s
    simp [ref, hk]

theorem some_design_fails : ∃ f : Decide, ¬ Passes f := by
  refine ⟨fun _ => true, fun h => ?_⟩
  obtain ⟨_, _, h3, _⟩ := h
  have := h3 { pidKnown := true, alive := true, reused := false, age := none, staleAfter := 0 }
    rfl rfl rfl
  simp at this

end Recover
