import Recover
namespace Recover

/-- "A later process recovers an orphan whose owner PID is no longer alive". -/
def DeadOwnerRecovered (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.alive = false → f c = true

/-- "The owner is gone when its pid is dead or now names a later process". -/
def ReusedPidRecovered (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.reused = true → f c = true

/-- "Remove only an orphaned lock": a live, unreused owner keeps its lock. -/
def LiveOwnerKept (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = true → c.alive = true → c.reused = false → f c = false

/-- "malformed/unknown owners are recovered after `stale_after` seconds". -/
def UnknownOwnerOldRecovered (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = false → ∀ a, c.age = some a → a ≥ c.staleAfter → f c = true

/-- "`stale_after` is only used when an owner cannot be identified safely":
with a known owner, the age and `stale_after` do not change the result. -/
def StaleAfterIgnoredForKnownOwner (f : Decide) : Prop :=
  ∀ c d : Case, c.pidKnown = true → d.pidKnown = true →
    c.alive = d.alive → c.reused = d.reused → f c = f d

/-- "Remove only an orphaned lock": an unknown owner younger than `stale_after` is kept. -/
def UnknownOwnerYoungKept (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = false → ∀ a, c.age = some a → a < c.staleAfter → f c = false

/-- "Remove only an orphaned lock": an unknown owner whose age is also unknown is kept,
because nothing shows the lock is older than `stale_after`. -/
def UnknownOwnerUnknownAgeKept (f : Decide) : Prop :=
  ∀ c : Case, c.pidKnown = false → c.age = none → f c = false

def Passes (f : Decide) : Prop :=
  DeadOwnerRecovered f ∧ ReusedPidRecovered f ∧ LiveOwnerKept f ∧
  UnknownOwnerOldRecovered f ∧ StaleAfterIgnoredForKnownOwner f ∧ UnknownOwnerYoungKept f ∧
  UnknownOwnerUnknownAgeKept f

theorem ref_passes : Passes ref := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hp ha; simp [ref, hp, ha]
  · intro c hp hr; simp [ref, hp, hr]
  · intro c hp ha hr; simp [ref, hp, ha, hr]
  · intro c hp a hage hge; simp [ref, hp, hage]; omega
  · intro c d hc hd ha hr; simp [ref, hc, hd, ha, hr]
  · intro c hp a hage hlt; simp [ref, hp, hage]; omega
  · intro c hp hage; simp [ref, hp, hage]

theorem some_design_fails : ∃ f : Decide, ¬ Passes f := by
  refine ⟨fun _ => false, ?_⟩
  intro h
  have := h.1 ⟨true, false, false, none, 0⟩ rfl rfl
  simp at this

end Recover
