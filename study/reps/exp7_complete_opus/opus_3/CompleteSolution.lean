/-
Hard Proof, experiment 7. AGENT-OWNED FILE.

The laws are complete for the critical section. The OS part of the state does
not depend on the design. The laws force each change of `cs`:
- acquire: an empty critical section must grant (Law 2), a full one must
  refuse a new process (Law 1), and a refusal to the holder changes nothing.
- release: the holder leaves (Law 4), and for any other process the release
  cannot change `cs`.
- spawn and exit do not depend on the design.
-/
import Laws

open Laws

namespace Complete

theorem replay_snoc {I : LockImpl} (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

/-- The OS after an event. It does not depend on the design. -/
def osAfter (os : OS) : Event → OS
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

theorem step_os (I : LockImpl) (s : State I) (e : Event) :
    (step I s e).os = osAfter s.os e := by
  cases e with
  | spawn pid =>
    simp only [step, osAfter]
    cases s.os.table pid <;> rfl
  | exit pid =>
    simp only [step, osAfter]
    cases s.os.table pid <;> rfl
  | acquire pid =>
    simp only [step, osAfter]
    cases s.os.table pid with
    | none => rfl
    | some t => cases grants I s <;> rfl
  | release pid =>
    simp only [step, osAfter]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl

theorem spawn_cs (I : LockImpl) (s : State I) (pid : Nat) :
    (step I s (.spawn pid)).cs = s.cs := by
  simp only [step]
  cases s.os.table pid <;> rfl

theorem exit_cs (I : LockImpl) (s : State I) (pid : Nat) :
    (step I s (.exit pid)).cs =
      (match s.os.table pid with
       | none => s.cs
       | some t => setCS s.cs ⟨pid, t⟩ false) := by
  simp only [step]
  cases s.os.table pid <;> rfl

theorem acquire_none (I : LockImpl) (s : State I) (pid : Nat)
    (h : s.os.table pid = none) : (step I s (.acquire pid)).cs = s.cs := by
  simp only [step, h]

theorem release_none (I : LockImpl) (s : State I) (pid : Nat)
    (h : s.os.table pid = none) : (step I s (.release pid)).cs = s.cs := by
  simp only [step, h]

theorem setCS_same (c : Proc → Bool) (p : Proc) (b : Bool) (h : c p = b) :
    setCS c p b = c := by
  funext q
  unfold setCS
  split
  · rename_i hq; subst hq; exact h.symm
  · rfl

/-- The laws force the effect of an acquire on `cs`. -/
theorem acquire_char (I : LockImpl) (hI : Passes I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t) :
    ((∀ q, (replay I evs).cs q = false) →
        (step I (replay I evs) (.acquire pid)).cs = setCS (replay I evs).cs ⟨pid, t⟩ true) ∧
    ((∃ q, (replay I evs).cs q = true) →
        (step I (replay I evs) (.acquire pid)).cs = (replay I evs).cs) := by
  obtain ⟨hMutex, hNoOrphan, _, _, _, _⟩ := hI
  have hstep := replay_snoc (I := I) evs (.acquire pid)
  cases hg : grants I (replay I evs) with
  | false =>
    have hs : (step I (replay I evs) (.acquire pid)).cs = (replay I evs).cs := by
      simp only [step, ht, hg, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, fun _ => hs⟩
    intro hall
    obtain ⟨q, hq, _⟩ := hNoOrphan evs hg
    rw [hall q] at hq
    cases hq
  | true =>
    have hs : (step I (replay I evs) (.acquire pid)).cs
        = setCS (replay I evs).cs ⟨pid, t⟩ true := by
      simp only [step, ht, hg, ↓reduceIte]
    refine ⟨fun _ => hs, ?_⟩
    intro ⟨q, hq⟩
    have hq' : (replay I (evs ++ [.acquire pid])).cs q = true := by
      rw [hstep, hs]
      unfold setCS
      split
      · rfl
      · exact hq
    have hr' : (replay I (evs ++ [.acquire pid])).cs ⟨pid, t⟩ = true := by
      rw [hstep, hs]
      simp [setCS]
    have heq : q = ⟨pid, t⟩ := hMutex _ q ⟨pid, t⟩ hq' hr'
    rw [hs]
    subst heq
    exact setCS_same _ _ _ hq

/-- The laws force the effect of a release on `cs`. -/
theorem release_char (I : LockImpl) (hI : Passes I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t) :
    (step I (replay I evs) (.release pid)).cs = setCS (replay I evs).cs ⟨pid, t⟩ false := by
  obtain ⟨_, _, _, hFree, _, _⟩ := hI
  have hstep := replay_snoc (I := I) evs (.release pid)
  have hor : (step I (replay I evs) (.release pid)).cs = (replay I evs).cs ∨
      (step I (replay I evs) (.release pid)).cs = setCS (replay I evs).cs ⟨pid, t⟩ false := by
    simp only [step, ht]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  cases hc : (replay I evs).cs ⟨pid, t⟩ with
  | false =>
    rw [setCS_same _ _ _ hc]
    rcases hor with h | h
    · exact h
    · rw [h, setCS_same _ _ _ hc]
  | true =>
    rcases hor with h | h
    · exfalso
      have hf := hFree evs ⟨pid, t⟩ hc
      rw [hstep, h, hc] at hf
      cases hf
    · exact h

theorem agree (I J : LockImpl) (hI : Passes I) (hJ : Passes J) :
    ∀ evs : List Event,
      (replay I evs).os = (replay J evs).os ∧ (replay I evs).cs = (replay J evs).cs := by
  intro evs
  rw [← List.reverse_reverse evs]
  generalize evs.reverse = l
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons e l ih =>
    rw [List.reverse_cons]
    obtain ⟨hos, hcs⟩ := ih
    rw [replay_snoc, replay_snoc]
    refine ⟨by rw [step_os, step_os, hos], ?_⟩
    cases e with
    | spawn pid => rw [spawn_cs, spawn_cs, hcs]
    | exit pid => rw [exit_cs, exit_cs, hos, hcs]
    | acquire pid =>
      cases ht : (replay J l.reverse).os.table pid with
      | none =>
        have htI : (replay I l.reverse).os.table pid = none := by rw [hos]; exact ht
        rw [acquire_none _ _ _ htI, acquire_none _ _ _ ht, hcs]
      | some t =>
        have htI : (replay I l.reverse).os.table pid = some t := by rw [hos]; exact ht
        have cI := acquire_char I hI l.reverse pid t htI
        have cJ := acquire_char J hJ l.reverse pid t ht
        by_cases hex : ∃ q, (replay J l.reverse).cs q = true
        · have hexI : ∃ q, (replay I l.reverse).cs q = true := by rw [hcs]; exact hex
          rw [cI.2 hexI, cJ.2 hex, hcs]
        · have hall : ∀ q, (replay J l.reverse).cs q = false := by
            intro q
            cases hq : (replay J l.reverse).cs q with
            | false => rfl
            | true => exact absurd ⟨q, hq⟩ hex
          have hallI : ∀ q, (replay I l.reverse).cs q = false := by rw [hcs]; exact hall
          rw [cI.1 hallI, cJ.1 hall, hcs]
    | release pid =>
      cases ht : (replay J l.reverse).os.table pid with
      | none =>
        have htI : (replay I l.reverse).os.table pid = none := by rw [hos]; exact ht
        rw [release_none _ _ _ htI, release_none _ _ _ ht, hcs]
      | some t =>
        have htI : (replay I l.reverse).os.table pid = some t := by rw [hos]; exact ht
        rw [release_char I hI _ pid t htI, release_char J hJ _ pid t ht, hcs]

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  rw [(agree I J hI hJ evs).2]

end Complete
