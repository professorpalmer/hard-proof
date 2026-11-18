/-
Hard Proof, experiment 4. The challenge of experiment 4 has no solution.

No lock design satisfies Law 1, Law 2, and Requirement 4 together. A lock whose
record ignores the start token cannot tell two states apart:
  A: process 5 took the lock and died, and a new process has pid 5.
  B: the new process with pid 5 took the lock.
Law 2 says that the lock must grant in A. Law 1 says that it must refuse in B.
-/
import Laws

open Laws

namespace Exp4

def A : List Event := [.spawn 5, .acquire 5, .exit 5, .spawn 5, .spawn 6]
def B : List Event := [.spawn 5, .exit 5, .spawn 5, .acquire 5, .spawn 6]

theorem no_lock_satisfies_all (I : LockImpl) (hm : Mutex I) (hn : NoOrphanHold I)
    (hr : RecordIgnoresToken I) : False := by
  have hAowner : (replay I A).owner = some (I.record ⟨5, 0⟩) := rfl
  have hBowner : (replay I B).owner = some (I.record ⟨5, 1⟩) := rfl
  have hos : (replay I B).os = (replay I A).os := rfl
  have hAcs : ∀ q, (replay I A).cs q = false := by
    intro q
    show (if q = ⟨5, 0⟩ then false else (if q = ⟨5, 0⟩ then true else false)) = false
    by_cases hq : q = ⟨5, 0⟩ <;> simp [hq]
  have hBcs : (replay I B).cs ⟨5, 1⟩ = true := rfl
  have hrec : I.record ⟨5, 1⟩ = I.record ⟨5, 0⟩ := hr 5 1 0
  cases hb : I.alive (replay I A).os (I.record ⟨5, 0⟩) with
  | true =>
    have hg : grants I (replay I A) = false := by
      simp only [grants, hAowner, hb, Bool.not_true]
    obtain ⟨q, hq, _⟩ := hn A hg
    rw [hAcs q] at hq
    cases hq
  | false =>
    have hg : grants I (replay I B) = true := by
      simp only [grants, hBowner, hos, hrec, hb, Bool.not_false]
    have hsnoc : replay I (B ++ [.acquire 6]) = step I (replay I B) (.acquire 6) := by
      simp [replay, List.foldl_append]
    have hstep : step I (replay I B) (.acquire 6) =
        { replay I B with owner := some (I.record ⟨6, 2⟩)
                          cs := setCS (replay I B).cs ⟨6, 2⟩ true } := by
      show (if grants I (replay I B) = true then _ else _) = _
      simp only [hg, ↓reduceIte]
      rfl
    have h6 : (replay I (B ++ [.acquire 6])).cs ⟨6, 2⟩ = true := by
      rw [hsnoc, hstep]; simp [setCS]
    have h5 : (replay I (B ++ [.acquire 6])).cs ⟨5, 1⟩ = true := by
      rw [hsnoc, hstep]
      show (if (⟨5, 1⟩ : Proc) = ⟨6, 2⟩ then true else (replay I B).cs ⟨5, 1⟩) = true
      rw [hBcs]; simp
    have heq := hm _ _ _ h5 h6
    exact absurd heq (by decide)

/-- The challenge of experiment 4 has no solution. -/
theorem challenge_is_impossible :
    ¬ ∃ I : LockImpl, Mutex I ∧ NoOrphanHold I ∧ RecordIgnoresToken I :=
  fun ⟨I, hm, hn, hr⟩ => no_lock_satisfies_all I hm hn hr

end Exp4

#print axioms Exp4.challenge_is_impossible
