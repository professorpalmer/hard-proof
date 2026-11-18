/-
Hard Proof, experiment 7. AGENT-OWNED FILE.

The laws are complete. After each event, the critical-section set is a function
of the OS and the old critical-section set only:

* acquire: when a process is in the critical section, Mutex forces no change.
  When no process is in it, NoOrphanHold forces a grant.
* release: ReleaseFrees forces the caller out. A design can only remove the
  caller, so the result is `setCS cs caller false` in each case.
* spawn and exit do not read the design.
-/
import Laws

open Laws

namespace Complete

theorem replay_snoc (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

/-- The OS part of a step. It does not read the design. -/
def osStep (os : OS) : Event → OS
  | .spawn pid =>
    match os.table pid with
    | some _ => os
    | none => { table := setTable os.table pid (some os.next), next := os.next + 1 }
  | .exit pid =>
    match os.table pid with
    | none => os
    | some _ => { os with table := setTable os.table pid none }
  | .acquire _ => os
  | .release _ => os

theorem os_step (I : LockImpl) (s : State I) (e : Event) :
    (step I s e).os = osStep s.os e := by
  cases e with
  | spawn pid =>
    simp only [step, osStep]
    cases s.os.table pid <;> rfl
  | exit pid =>
    simp only [step, osStep]
    cases s.os.table pid <;> rfl
  | acquire pid =>
    simp only [step, osStep]
    cases s.os.table pid with
    | none => rfl
    | some t => simp only []; split <;> rfl
  | release pid =>
    simp only [step, osStep]
    cases s.os.table pid with
    | none => rfl
    | some t =>
      simp only []
      cases s.owner with
      | none => rfl
      | some r => simp only []; split <;> rfl

open Classical in
/-- The critical-section part of a step, for a design that passes the laws. -/
noncomputable def csStep (os : OS) (c : Proc → Bool) : Event → (Proc → Bool)
  | .spawn _ => c
  | .exit pid =>
    match os.table pid with
    | none => c
    | some t => setCS c ⟨pid, t⟩ false
  | .acquire pid =>
    match os.table pid with
    | none => c
    | some t => if (∃ p, c p = true) then c else setCS c ⟨pid, t⟩ true
  | .release pid =>
    match os.table pid with
    | none => c
    | some t => setCS c ⟨pid, t⟩ false

theorem setCS_same (c : Proc → Bool) (p : Proc) (b : Bool) (h : c p = b) :
    setCS c p b = c := by
  funext q
  unfold setCS
  split
  · next heq => subst heq; exact h.symm
  · rfl

theorem setCS_at (c : Proc → Bool) (p : Proc) (b : Bool) : setCS c p b p = b := by
  simp [setCS]

theorem setCS_ne (c : Proc → Bool) (p q : Proc) (b : Bool) (h : q ≠ p) :
    setCS c p b q = c q := by
  simp [setCS, h]

/-- A release can only take the caller out. -/
theorem release_shape (I : LockImpl) (s : State I) (pid t : Nat)
    (ht : s.os.table pid = some t) :
    (step I s (.release pid)).cs = s.cs ∨
      (step I s (.release pid)).cs = setCS s.cs ⟨pid, t⟩ false := by
  simp only [step, ht]
  cases s.owner with
  | none => exact Or.inl rfl
  | some r =>
    simp only []
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem cs_step (I : LockImpl) (hP : Passes I) (evs : List Event) (e : Event) :
    (replay I (evs ++ [e])).cs = csStep (replay I evs).os (replay I evs).cs e := by
  obtain ⟨hMutex, hNoOrphan, _, hRelease, _, _⟩ := hP
  cases e with
  | spawn pid =>
    rw [replay_snoc]
    simp only [step, csStep]
    cases (replay I evs).os.table pid <;> rfl
  | exit pid =>
    rw [replay_snoc]
    simp only [step, csStep]
    cases (replay I evs).os.table pid <;> rfl
  | acquire pid =>
    cases ht : (replay I evs).os.table pid with
    | none =>
      rw [replay_snoc]
      simp only [step, csStep, ht]
    | some t =>
      by_cases hex : ∃ p, (replay I evs).cs p = true
      · have hspec : csStep (replay I evs).os (replay I evs).cs (.acquire pid)
            = (replay I evs).cs := by
          simp only [csStep, ht, if_pos hex]
        rw [hspec]
        obtain ⟨p, hp⟩ := hex
        by_cases hg : grants I (replay I evs) = true
        · have hcs : (replay I (evs ++ [.acquire pid])).cs
              = setCS (replay I evs).cs ⟨pid, t⟩ true := by
            rw [replay_snoc]; simp only [step, ht, hg, if_true]
          by_cases hpq : p = ⟨pid, t⟩
          · rw [hcs]; subst hpq; exact setCS_same _ _ _ hp
          · exfalso
            have h1 : (replay I (evs ++ [.acquire pid])).cs ⟨pid, t⟩ = true := by
              rw [hcs]; exact setCS_at _ _ _
            have h2 : (replay I (evs ++ [.acquire pid])).cs p = true := by
              rw [hcs, setCS_ne _ _ _ _ hpq]; exact hp
            exact hpq (hMutex _ _ _ h2 h1)
        · have hg' : grants I (replay I evs) = false := by
            cases h : grants I (replay I evs)
            · rfl
            · exact absurd h hg
          rw [replay_snoc]; simp only [step, ht, hg', Bool.false_eq_true, if_false]
      · have hg : grants I (replay I evs) = true := by
          cases h : grants I (replay I evs)
          · exfalso
            obtain ⟨q, hq, _⟩ := hNoOrphan evs h
            exact hex ⟨q, hq⟩
          · rfl
        rw [replay_snoc]
        simp only [step, csStep, ht, hg, if_true, if_neg hex]
  | release pid =>
    cases ht : (replay I evs).os.table pid with
    | none =>
      rw [replay_snoc]
      simp only [step, csStep, ht]
    | some t =>
      have hspec : csStep (replay I evs).os (replay I evs).cs (.release pid)
          = setCS (replay I evs).cs ⟨pid, t⟩ false := by
        simp only [csStep, ht]
      rw [hspec]
      have hshape := release_shape I (replay I evs) pid t ht
      rw [← replay_snoc] at hshape
      by_cases hq : (replay I evs).cs ⟨pid, t⟩ = true
      · have hfree := hRelease evs ⟨pid, t⟩ hq
        rcases hshape with h | h
        · exfalso
          have : (replay I (evs ++ [Event.release pid])).cs ⟨pid, t⟩ = true := by
            rw [h]; exact hq
          rw [hfree] at this
          exact Bool.false_ne_true this
        · exact h
      · have hf : (replay I evs).cs ⟨pid, t⟩ = false := by
          cases h : (replay I evs).cs ⟨pid, t⟩
          · rfl
          · exact absurd h hq
        rw [setCS_same _ _ _ hf]
        rcases hshape with h | h
        · exact h
        · rw [h, setCS_same _ _ _ hf]

theorem snoc_ind {P : List Event → Prop} (h0 : P [])
    (hs : ∀ l e, P l → P (l ++ [e])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons e es ih => rw [List.reverse_cons]; exact hs _ _ ih

theorem both (I J : LockImpl) (hI : Passes I) (hJ : Passes J) (evs : List Event) :
    (replay I evs).os = (replay J evs).os ∧ (replay I evs).cs = (replay J evs).cs := by
  induction evs using snoc_ind with
  | h0 => exact ⟨rfl, rfl⟩
  | hs evs e ih =>
    obtain ⟨hos, hcs⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [replay_snoc, replay_snoc, os_step, os_step, hos]
    · rw [cs_step I hI, cs_step J hJ, hos, hcs]

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  rw [(both I J hI hJ evs).2]

end Complete
