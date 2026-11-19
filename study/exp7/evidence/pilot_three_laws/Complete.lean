import Laws

open Laws

namespace Complete

/-- Law 4. A release by the process in the critical section frees the lock. -/
def ReleaseFrees (I : LockImpl) : Prop :=
  ∀ (evs : List Event) (p : Proc),
    (replay I evs).cs p = true →
      (replay I (evs ++ [Event.release p.pid])).cs p = false

theorem replay_snoc {I : LockImpl} (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

/-- Induction on a list from the right end. -/
theorem snoc_induction {α : Type} {P : List α → Prop} (hnil : P [])
    (hsnoc : ∀ (l : List α) (a : α), P l → P (l ++ [a])) : ∀ l, P l := by
  have h : ∀ l : List α, P l.reverse := by
    intro l
    induction l with
    | nil => exact hnil
    | cons a t ih => rw [List.reverse_cons]; exact hsnoc _ _ ih
  intro l
  have := h l.reverse
  rwa [List.reverse_reverse] at this

/-- The OS part of a step does not depend on the lock design. -/
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

theorem step_os (I : LockImpl) (s : State I) (e : Event) : (step I s e).os = osStep s.os e := by
  cases e with
  | spawn pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | exit pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | acquire pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some t =>
      simp only [step, osStep, h]
      split <;> rfl
  | release pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some t =>
      simp only [step, osStep, h]
      split
      · rfl
      · split <;> rfl

theorem replay_os (I J : LockImpl) : ∀ evs, (replay I evs).os = (replay J evs).os := by
  apply snoc_induction
  · rfl
  · intro l a ih
    rw [replay_snoc, replay_snoc, step_os, step_os, ih]

/-- Who is in the critical section after one more event. The formula uses only
the OS state and the set before the event. It does not name a lock design. -/
def NextIn (os : OS) (cs : Proc → Bool) (e : Event) (p' : Proc) : Prop :=
  match e with
  | .spawn _ => cs p' = true
  | .exit pid => cs p' = true ∧ ¬ (p'.pid = pid ∧ os.table pid = some p'.tok)
  | .acquire pid =>
    cs p' = true ∨ (p'.pid = pid ∧ os.table pid = some p'.tok ∧ ∀ q, cs q = false)
  | .release pid => cs p' = true ∧ ¬ (p'.pid = pid ∧ os.table pid = some p'.tok)

theorem proc_eq_iff (p' : Proc) (pid t : Nat) : p' = ⟨pid, t⟩ ↔ (p'.pid = pid ∧ p'.tok = t) := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩; subst h1; subst h2; rfl

/-- A design that obeys laws 1, 2 and 4 moves the critical section as `NextIn` says. -/
theorem next_cs (I : LockImpl) (hM : Mutex I) (hN : NoOrphanHold I) (hR : ReleaseFrees I)
    (evs : List Event) (e : Event) (p' : Proc) :
    (replay I (evs ++ [e])).cs p' = true ↔
      NextIn (replay I evs).os (replay I evs).cs e p' := by
  have hM' := hM (evs ++ [e])
  have hR' : ∀ p : Proc, (replay I evs).cs p = true →
      (step I (replay I evs) (Event.release p.pid)).cs p = false := by
    intro p h
    have := hR evs p h
    rwa [replay_snoc] at this
  rw [replay_snoc] at hM' ⊢
  have hN' := hN evs
  generalize replay I evs = s at *
  cases e with
  | spawn pid =>
    simp only [NextIn, step]
    split <;> rfl
  | exit pid =>
    simp only [NextIn]
    cases hpid : s.os.table pid with
    | none => simp [step, hpid]
    | some t =>
      simp only [step, hpid, setCS]
      by_cases hp : p' = ⟨pid, t⟩
      · subst hp; simp
      · have : ¬ (p'.pid = pid ∧ some t = some p'.tok) := by
          intro ⟨h1, h2⟩; apply hp; exact (proc_eq_iff _ _ _).2 ⟨h1, (Option.some.inj h2).symm⟩
        simp only [hp, ↓reduceIte]
        constructor
        · intro h; exact ⟨h, this⟩
        · intro h; exact h.1
  | acquire pid =>
    simp only [NextIn]
    cases hpid : s.os.table pid with
    | none => simp [step, hpid]
    | some t =>
      cases hg : grants I s with
      | false =>
        have hstep : step I s (.acquire pid) = s := by simp only [step, hpid, hg, Bool.false_eq_true, ↓reduceIte]
        rw [hstep]
        obtain ⟨q, hq, _⟩ := hN' hg
        constructor
        · intro h; exact Or.inl h
        · intro h
          rcases h with h | ⟨_, _, hempty⟩
          · exact h
          · rw [hempty q] at hq; cases hq
      | true =>
        have hstep : (step I s (.acquire pid)).cs = setCS s.cs ⟨pid, t⟩ true := by
          simp only [step, hpid, hg, ↓reduceIte]
        rw [hstep] at hM'
        rw [hstep]
        simp only [setCS]
        by_cases hp : p' = ⟨pid, t⟩
        · subst hp
          simp only [↓reduceIte, true_iff]
          by_cases hin : s.cs ⟨pid, t⟩ = true
          · exact Or.inl hin
          · right
            refine ⟨by first | rfl | trivial, by first | rfl | trivial, ?_⟩
            intro q
            cases hq : s.cs q with
            | false => rfl
            | true =>
              exfalso
              have hqne : q ≠ ⟨pid, t⟩ := by intro h; subst h; exact hin hq
              have h1 : setCS s.cs ⟨pid, t⟩ true q = true := by simp [setCS, hqne, hq]
              have h2 : setCS s.cs ⟨pid, t⟩ true ⟨pid, t⟩ = true := by simp [setCS]
              exact hqne (hM' q ⟨pid, t⟩ h1 h2)
        · simp only [hp, ↓reduceIte]
          constructor
          · intro h; exact Or.inl h
          · intro h
            rcases h with h | ⟨h1, h2, _⟩
            · exact h
            · exact absurd ((proc_eq_iff _ _ _).2 ⟨h1, (Option.some.inj h2).symm⟩) hp
  | release pid =>
    simp only [NextIn]
    cases hpid : s.os.table pid with
    | none => simp [step, hpid]
    | some t =>
      have hshape : (step I s (.release pid)).cs = s.cs ∨
          (step I s (.release pid)).cs = setCS s.cs ⟨pid, t⟩ false := by
        simp only [step, hpid]
        split
        · left; rfl
        · split
          · right; rfl
          · left; rfl
      have hfree : s.cs ⟨pid, t⟩ = true → (step I s (.release pid)).cs ⟨pid, t⟩ = false := by
        intro h
        exact hR' ⟨pid, t⟩ h
      have hiff : (p'.pid = pid ∧ some t = some p'.tok) ↔ p' = ⟨pid, t⟩ := by
        constructor
        · intro ⟨h1, h2⟩; exact (proc_eq_iff _ _ _).2 ⟨h1, (Option.some.inj h2).symm⟩
        · intro h; subst h; exact ⟨rfl, rfl⟩
      rw [hiff]
      rcases hshape with hsame | hset
      · rw [hsame]
        constructor
        · intro h
          refine ⟨h, ?_⟩
          intro hp; subst hp
          have := hfree h
          rw [hsame] at this
          rw [this] at h; cases h
        · intro h; exact h.1
      · rw [hset]
        simp only [setCS]
        by_cases hp : p' = ⟨pid, t⟩
        · simp [hp]
        · simp [hp]

/-- Completeness. Two designs that obey laws 1, 2 and 4 put the same processes
in the critical section after each sequence of events. -/
theorem complete (I J : LockImpl)
    (hI : Mutex I ∧ NoOrphanHold I ∧ ReleaseFrees I)
    (hJ : Mutex J ∧ NoOrphanHold J ∧ ReleaseFrees J) :
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  apply snoc_induction
  · intro p; rfl
  · intro l a ih p
    have hcs : (replay I l).cs = (replay J l).cs := funext ih
    have hos := replay_os I J l
    have hi := next_cs I hI.1 hI.2.1 hI.2.2 l a p
    have hj := next_cs J hJ.1 hJ.2.1 hJ.2.2 l a p
    rw [hcs, hos] at hi
    have : (replay I (l ++ [a])).cs p = true ↔ (replay J (l ++ [a])).cs p = true := hi.trans hj.symm
    cases h1 : (replay I (l ++ [a])).cs p <;> cases h2 : (replay J (l ++ [a])).cs p <;> simp_all

end Complete

#print axioms Complete.complete
