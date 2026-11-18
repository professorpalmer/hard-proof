import Laws
import Mutants

open Laws

/-- No lock design satisfies Law 1, Law 2 and Requirement 4 together. -/
theorem no_lock_all_three (L : LockImpl) (hM : Mutex L) (hN : NoOrphanHold L)
    (hR : RecordIgnoresToken L) : False := by
  -- X: pid 2 is alive. Pid 1 gets token 2 and acquires.
  -- Y: pid 2 is alive. Pid 1 gets token 1, acquires, exits, then gets token 2.
  -- X and Y have the same OS, and the owner record of pid 1 is the same in both.
  have hOS : (replay L [.spawn 2, .spawn 9, .exit 9, .spawn 1, .acquire 1]).os
      = (replay L [.spawn 2, .spawn 1, .acquire 1, .exit 1, .spawn 1]).os := by
    simp [replay, step, init, setTable, grants]
    funext q
    by_cases h1 : q = 1 <;> by_cases h2 : q = 2 <;> by_cases h9 : q = 9 <;> simp_all [setTable]
  have hOwnerX : (replay L [.spawn 2, .spawn 9, .exit 9, .spawn 1, .acquire 1]).owner
      = some (L.record ⟨1, 2⟩) := by
    simp [replay, step, init, setTable, grants]
  have hOwnerY : (replay L [.spawn 2, .spawn 1, .acquire 1, .exit 1, .spawn 1]).owner
      = some (L.record ⟨1, 1⟩) := by
    simp [replay, step, init, setTable, grants]
  have hCsY : ∀ q, (replay L [.spawn 2, .spawn 1, .acquire 1, .exit 1, .spawn 1]).cs q = false := by
    intro q
    simp [replay, step, init, setTable, grants, setCS]
  -- Law 1: the owner in X is alive, so the lock refuses pid 2.
  have hGrantX : grants L (replay L [.spawn 2, .spawn 9, .exit 9, .spawn 1, .acquire 1]) = false := by
    cases hg : grants L (replay L [.spawn 2, .spawn 9, .exit 9, .spawn 1, .acquire 1]) with
    | false => rfl
    | true =>
      have h := hM [.spawn 2, .spawn 9, .exit 9, .spawn 1, .acquire 1, .acquire 2]
        ⟨2, 0⟩ ⟨1, 2⟩ (by
          simp [replay, step, init, setTable, grants, setCS] at hg ⊢
          simp_all [setCS])
        (by
          simp [replay, step, init, setTable, grants, setCS] at hg ⊢
          simp_all [setCS])
      exact absurd h (by decide)
  -- Requirement 4: the owner records of X and Y are equal.
  have hRec : L.record ⟨1, 2⟩ = L.record ⟨1, 1⟩ := hR 1 2 1
  have hGrantY : grants L (replay L [.spawn 2, .spawn 1, .acquire 1, .exit 1, .spawn 1]) = false := by
    simp only [grants, hOS, hOwnerX, hOwnerY, hRec] at hGrantX ⊢
    exact hGrantX
  -- Law 2: a refusal needs a process in the critical section. Y has none.
  obtain ⟨q, hq, _⟩ := hN [.spawn 2, .spawn 1, .acquire 1, .exit 1, .spawn 1] hGrantY
  rw [hCsY q] at hq
  exact Bool.false_ne_true hq

#print axioms no_lock_all_three
