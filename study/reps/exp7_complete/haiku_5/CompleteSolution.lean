/-
Hard Proof, experiment 7. AGENT-OWNED FILE.

Completeness proof. Two designs that pass each law put the same processes in
the critical section after each trace.

Idea. The OS state does not depend on the design. The critical section changes
only through a granted acquire and through a release. A granted acquire by a
requester outside the critical section happens exactly when no live process is
in the critical section: Mutex rules out a grant when one is, and NoOrphanHold
rules out a refusal when none is. A release of a process in the critical section
clears it, by ReleaseFrees. So the pair (OS, critical section) is the same for
both designs after every prefix of a trace.
-/
import Laws

open Laws

namespace Complete

/-- Replay of a snoc. -/
theorem replay_snoc' {I : LockImpl} (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

/-- Two designs agree on the OS and on the critical section after a trace. -/
def Agree (I J : LockImpl) (pre : List Event) : Prop :=
  (replay I pre).os = (replay J pre).os ∧ (replay I pre).cs = (replay J pre).cs

/-- A granted acquire by a live requester outside the critical section happens
exactly when no live process is in the critical section. -/
theorem grants_iff {I : LockImpl} (hI : Passes I) (pre : List Event) (pid tok : Nat)
    (ht : (replay I pre).os.table pid = some tok)
    (hc : (replay I pre).cs ⟨pid, tok⟩ = false) :
    grants I (replay I pre) = true ↔
      ¬ ∃ q : Proc, (replay I pre).cs q = true ∧ (replay I pre).os.live q := by
  have hM : Mutex I := hI.1
  have hN : NoOrphanHold I := hI.2.1
  constructor
  · intro hg hbusy
    obtain ⟨q, hq, hql⟩ := hbusy
    have hne : q ≠ ⟨pid, tok⟩ := by
      intro h; subst h; rw [hc] at hq; cases hq
    have hacq : (replay I (pre ++ [Event.acquire pid])).cs q = true := by
      rw [replay_snoc']
      simp only [step, ht, hg, if_true, setCS, hne, if_false]
      exact hq
    have hself : (replay I (pre ++ [Event.acquire pid])).cs ⟨pid, tok⟩ = true := by
      rw [replay_snoc']
      simp only [step, ht, hg, if_true, setCS]
    exact hne (hM (pre ++ [Event.acquire pid]) q ⟨pid, tok⟩ hacq hself)
  · intro hnb
    cases hg : grants I (replay I pre) with
    | true => rfl
    | false =>
      obtain ⟨q, hq, hql⟩ := hN pre hg
      exact (hnb ⟨q, hq, hql⟩).elim

/-- A release never changes the OS. -/
theorem step_release_os {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (Event.release pid)).os = s.os := by
  simp only [step]
  cases ht : s.os.table pid with
  | none => simp [ht]
  | some t0 =>
    simp only [ht]
    cases ho : s.owner with
    | none => rfl
    | some r0 =>
      simp only [ho]
      split <;> rfl

/-- A release of a process outside the critical section keeps it outside. -/
theorem release_false_state {I : LockImpl} (s : State I) (pid tok : Nat)
    (ht : s.os.table pid = some tok) (hc : s.cs ⟨pid, tok⟩ = false) :
    (step I s (Event.release pid)).cs ⟨pid, tok⟩ = false := by
  simp only [step, ht]
  cases ho : s.owner with
  | none => simp only [ho]; exact hc
  | some r0 =>
    simp only [ho]
    split
    · simp [setCS]
    · exact hc

/-- A release by a process in the critical section clears it. -/
theorem release_cs {I : LockImpl} (hI : Passes I) (pre : List Event) (pid tok : Nat)
    (ht : (replay I pre).os.table pid = some tok) :
    (replay I (pre ++ [Event.release pid])).cs ⟨pid, tok⟩ = false := by
  have hRF : ReleaseFrees I := hI.2.2.2.1
  by_cases hc : (replay I pre).cs ⟨pid, tok⟩ = true
  · exact hRF pre ⟨pid, tok⟩ hc
  · have hc' : (replay I pre).cs ⟨pid, tok⟩ = false := by
      cases h : (replay I pre).cs ⟨pid, tok⟩
      · rfl
      · exact absurd h hc
    rw [replay_snoc']
    exact release_false_state (replay I pre) pid tok ht hc'

/-- A release by `pid` (holding token `tok`) changes the critical section only
at that process. -/
theorem release_cs_ne {I : LockImpl} (s : State I) (pid tok : Nat)
    (ht : s.os.table pid = some tok) (q : Proc) (hq : q ≠ ⟨pid, tok⟩) :
    (step I s (Event.release pid)).cs q = s.cs q := by
  simp only [step, ht]
  cases ho : s.owner with
  | none => simp only [ho]
  | some r0 =>
    simp only [ho]
    split
    · simp only [setCS]; rw [if_neg hq]
    · rfl

/-- A set to true on a process that is already in the critical section changes
nothing. -/
theorem setCS_true_self (c : Proc → Bool) (r : Proc) (hr : c r = true) :
    setCS c r true = c := by
  funext q
  by_cases h : q = r
  · subst h; simp [setCS, hr]
  · simp [setCS, h]

/-- One event keeps the OS and the critical section in agreement. -/
theorem step_pair {I J : LockImpl} (e : Event) (s : State I) (t : State J)
    (hos : s.os = t.os) (hcs : s.cs = t.cs)
    (hg : ∀ pid tok, s.os.table pid = some tok → s.cs ⟨pid, tok⟩ = false →
      grants I s = grants J t)
    (hrel : ∀ pid tok, s.os.table pid = some tok →
      (step I s (Event.release pid)).cs ⟨pid, tok⟩ = false ∧
      (step J t (Event.release pid)).cs ⟨pid, tok⟩ = false) :
    (step I s e).os = (step J t e).os ∧ (step I s e).cs = (step J t e).cs := by
  cases e with
  | spawn pid =>
    simp only [step, hos, hcs]
    split <;> simp_all
  | exit pid =>
    simp only [step, hos, hcs]
    split <;> simp_all
  | acquire pid =>
    cases ht : t.os.table pid with
    | none =>
      have hs : s.os.table pid = none := by rw [hos]; exact ht
      simp only [step, hs, ht]
      exact ⟨hos, hcs⟩
    | some tok =>
      have hs : s.os.table pid = some tok := by rw [hos]; exact ht
      by_cases hc : s.cs ⟨pid, tok⟩ = true
      · have hc' : t.cs ⟨pid, tok⟩ = true := by rw [← hcs]; exact hc
        have e1 := setCS_true_self s.cs ⟨pid, tok⟩ hc
        have e2 := setCS_true_self t.cs ⟨pid, tok⟩ hc'
        simp only [step, hs, ht]
        constructor <;> split <;> split <;> simp [e1, e2, hos, hcs]
      · have hc0 : s.cs ⟨pid, tok⟩ = false := by
          cases h : s.cs ⟨pid, tok⟩
          · rfl
          · exact absurd h hc
        have hgeq := hg pid tok hs hc0
        simp only [step, hs, ht, hgeq]
        by_cases hgJ : grants J t = true <;> simp [hgJ, hos, hcs]
  | release pid =>
    refine ⟨?_, ?_⟩
    · rw [step_release_os, step_release_os]; exact hos
    · cases ht : t.os.table pid with
      | none =>
        have hs : s.os.table pid = none := by rw [hos]; exact ht
        simp only [step, hs, ht]
        exact hcs
      | some tok =>
        have hs : s.os.table pid = some tok := by rw [hos]; exact ht
        have hr := hrel pid tok hs
        funext q
        by_cases hq : q = ⟨pid, tok⟩
        · subst hq
          rw [hr.1, hr.2]
        · rw [release_cs_ne s pid tok hs q hq,
            release_cs_ne t pid tok (by rw [← hos]; exact hs) q hq, hcs]

/-- The agreement invariant is preserved by one event. -/
theorem agree_step {I J : LockImpl} (hI : Passes I) (hJ : Passes J) (pre : List Event)
    (e : Event) (h : Agree I J pre) : Agree I J (pre ++ [e]) := by
  obtain ⟨hos, hcs⟩ := h
  have hg : ∀ pid tok, (replay I pre).os.table pid = some tok →
      (replay I pre).cs ⟨pid, tok⟩ = false →
      grants I (replay I pre) = grants J (replay J pre) := by
    intro pid tok ht hc
    have ht' : (replay J pre).os.table pid = some tok := by rw [← hos]; exact ht
    have hc' : (replay J pre).cs ⟨pid, tok⟩ = false := by rw [← hcs]; exact hc
    have gI := grants_iff hI pre pid tok ht hc
    have gJ := grants_iff hJ pre pid tok ht' hc'
    have hB : (¬ ∃ q : Proc, (replay I pre).cs q = true ∧ (replay I pre).os.live q) ↔
        (¬ ∃ q : Proc, (replay J pre).cs q = true ∧ (replay J pre).os.live q) := by
      rw [hos, hcs]
    rw [Bool.eq_iff_iff]
    exact gI.trans (hB.trans gJ.symm)
  have hrel : ∀ pid tok, (replay I pre).os.table pid = some tok →
      (step I (replay I pre) (Event.release pid)).cs ⟨pid, tok⟩ = false ∧
      (step J (replay J pre) (Event.release pid)).cs ⟨pid, tok⟩ = false := by
    intro pid tok ht
    have ht' : (replay J pre).os.table pid = some tok := by rw [← hos]; exact ht
    constructor
    · rw [← replay_snoc']; exact release_cs hI pre pid tok ht
    · rw [← replay_snoc']; exact release_cs hJ pre pid tok ht'
  have hstep := step_pair e (replay I pre) (replay J pre) hos hcs hg hrel
  unfold Agree
  rw [replay_snoc', replay_snoc']
  exact hstep

/-- Agreement holds after every trace, from the initial state. -/
theorem agree_all {I J : LockImpl} (hI : Passes I) (hJ : Passes J) :
    ∀ (es pre : List Event), Agree I J pre → Agree I J (pre ++ es) := by
  intro es
  induction es with
  | nil => intro pre h; simpa using h
  | cons e es ih =>
    intro pre h
    have h1 := agree_step hI hJ pre e h
    have h2 := ih (pre ++ [e]) h1
    simpa [List.append_assoc] using h2

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  have base : Agree I J [] := by
    constructor
    · simp [replay, init]
    · funext q; simp [replay, init]
  have h := agree_all hI hJ evs [] base
  simp only [List.nil_append] at h
  exact congrFun h.2 p

end Complete
