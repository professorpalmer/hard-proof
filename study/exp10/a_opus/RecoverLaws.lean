import Recover

namespace Recover

/-- "A later process recovers an orphan whose owner PID is no longer alive."
Also: "The owner is gone when its pid is dead". -/
def DeadOwnerRecovered (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.alive = false → f c = true

/-- "The owner is gone when its pid is dead or now names a later process
(the lock records the owner's identity, see `proc_identity`)." -/
def ReusedOwnerRecovered (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.reused = true → f c = true

/-- "Remove only an orphaned lock, with a guard against reclaim races."
An identified owner whose pid is alive and not reused is not gone. -/
def LiveOwnerKept (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.alive = true → c.reused = false → f c = false

/-- "malformed/unknown owners are recovered after `stale_after` seconds."
(Strictly after; the boundary `age = stale_after` is not clear.) -/
def UnknownStaleRecovered (f : Decide) : Prop :=
  ∀ c : Case, ∀ a : Nat, c.pidKnown = false → c.age = some a →
    a > c.staleAfter → f c = true

/-- "malformed/unknown owners are recovered after `stale_after` seconds."
with "Remove only an orphaned lock": an unknown owner younger than
`stale_after` is kept. -/
def UnknownFreshKept (f : Decide) : Prop :=
  ∀ c : Case, ∀ a : Nat, c.pidKnown = false → c.age = some a →
    a < c.staleAfter → f c = false

/-- "`stale_after` is only used when an owner cannot be identified safely."
When the owner pid is known, the age and `stale_after` do not change the
result. -/
def StaleAfterOnlyUnidentified (f : Decide) : Prop :=
  ∀ c : Case, ∀ age : Option Nat, ∀ s : Nat, c.pidKnown = true →
    f { c with age := age, staleAfter := s } = f c

def Passes (f : Decide) : Prop :=
  DeadOwnerRecovered f ∧ ReusedOwnerRecovered f ∧ LiveOwnerKept f ∧
  UnknownStaleRecovered f ∧ UnknownFreshKept f ∧ StaleAfterOnlyUnidentified f

theorem ref_passes : Passes ref := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hk ha
    simp [ref, hk, ha]
  · intro c hk hr
    simp [ref, hk, hr]
  · intro c hk ha hr
    simp [ref, hk, ha, hr]
  · intro c a hk hage hlt
    simp [ref, hk, hage]
    omega
  · intro c a hk hage hlt
    simp [ref, hk, hage]
    omega
  · intro c age s hk
    simp [ref, hk]

theorem some_design_fails : ∃ f : Decide, ¬ Passes f := by
  refine ⟨fun _ => false, ?_⟩
  intro h
  have := h.1 { pidKnown := true, alive := false, reused := false,
                age := none, staleAfter := 0 } rfl rfl
  cases this

end Recover
