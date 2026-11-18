import Laws
open Laws

/-- No lock design satisfies Law 1, Law 2 and Requirement 4 together. -/
theorem no_lock_meets_all (I : LockImpl)
    (hM : Mutex I) (hN : NoOrphanHold I) (hR : RecordIgnoresToken I) : False := by
  -- Y: pid 5 is reused, then the new process (token 1) takes the lock, then pid 6 starts.
  -- X: process (5, token 0) takes the lock and exits, pid 5 is reused, then pid 6 starts.
  -- X and Y have the same OS and the same owner record, so `grants` is equal.
  have hY : grants I (replay I [.spawn 5, .exit 5, .spawn 5, .acquire 5, .spawn 6]) = false := by
    cases hg : grants I (replay I [.spawn 5, .exit 5, .spawn 5, .acquire 5, .spawn 6]) with
    | false => rfl
    | true =>
      exfalso
      have h := hM [.spawn 5, .exit 5, .spawn 5, .acquire 5, .spawn 6, .acquire 6]
        ⟨5, 1⟩ ⟨6, 2⟩
        (by simp [replay, step, init, setTable, setCS, hg])
        (by simp [replay, step, init, setTable, setCS, hg])
      cases h
  have hX : grants I (replay I [.spawn 5, .acquire 5, .exit 5, .spawn 5, .spawn 6]) = false := by
    have heq := hR 5 0 1
    simp [replay, step, init, setTable, setCS, grants] at hY ⊢
    rw [heq]
    simpa using hY
  obtain ⟨q, hq, _⟩ := hN _ hX
  simp [replay, step, init, setTable, setCS] at hq
