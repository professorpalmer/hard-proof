/-
Hard Proof, experiment 7. AGENT-OWNED FILE.

Completeness proof. Two designs that pass each law put the same processes in
the critical section after each event sequence. The process table `os` does not
depend on the design. The critical section changes only by the rules that
Mutex, NoOrphanHold and ReleaseFrees fix.
-/
import Laws

open Laws

namespace Complete

theorem replay_snoc' {I : LockImpl} (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

/-- One step gives the same process table from the same process table. -/
theorem step_os_eq {I J : LockImpl} (s : State I) (t : State J) (h : s.os = t.os) (e : Event) :
    (step I s e).os = (step J t e).os := by
  obtain ⟨os, o, c⟩ := s
  obtain ⟨os', o', c'⟩ := t
  have h' : os = os' := h
  subst h'
  cases e with
  | spawn pid => rcases hT : os.table pid with _ | t0 <;> simp [step, hT]
  | exit pid => rcases hT : os.table pid with _ | t0 <;> simp [step, hT]
  | acquire pid =>
    rcases hT : os.table pid with _ | t0
    · simp [step, hT]
    · simp only [step, hT]
      by_cases hg : grants I { os := os, owner := o, cs := c } = true <;>
        by_cases hg' : grants J { os := os, owner := o', cs := c' } = true <;>
        simp [hg, hg']
  | release pid =>
    rcases hT : os.table pid with _ | t0
    · simp [step, hT]
    · simp only [step, hT]
      cases o <;> cases o' <;> dsimp only <;> (try split) <;> (try split) <;> simp_all

theorem cs_spawn {I : LockImpl} (evs : List Event) (pid : Nat) :
    (replay I (evs ++ [.spawn pid])).cs = (replay I evs).cs := by
  rw [replay_snoc']
  rcases hT : (replay I evs).os.table pid with _ | t0 <;> simp [step, hT]

theorem rel_none {I : LockImpl} (evs : List Event) (pid : Nat)
    (hT : (replay I evs).os.table pid = none) :
    (replay I (evs ++ [.release pid])).cs = (replay I evs).cs := by
  rw [replay_snoc']
  simp [step, hT]

theorem rel_other {I : LockImpl} (evs : List Event) (pid t : Nat)
    (hT : (replay I evs).os.table pid = some t) (x : Proc) (hx : x ≠ ⟨pid, t⟩) :
    (replay I (evs ++ [.release pid])).cs x = (replay I evs).cs x := by
  rw [replay_snoc']
  rcases ho : (replay I evs).owner with _ | r
  · simp [step, hT, ho]
  · rcases hio : I.isOwner r ⟨pid, t⟩ with _ | _
    · simp [step, hT, ho, hio]
    · simp [step, hT, ho, hio, setCS, hx]

theorem rel_q {I : LockImpl} (hR : ReleaseFrees I) (evs : List Event) (pid t : Nat)
    (hT : (replay I evs).os.table pid = some t) :
    (replay I (evs ++ [.release pid])).cs ⟨pid, t⟩ = false := by
  by_cases hc : (replay I evs).cs ⟨pid, t⟩ = true
  · exact hR evs ⟨pid, t⟩ hc
  · have hc' : (replay I evs).cs ⟨pid, t⟩ = false := by simpa using hc
    rw [replay_snoc']
    rcases ho : (replay I evs).owner with _ | r
    · simp [step, hT, ho, hc']
    · rcases hio : I.isOwner r ⟨pid, t⟩ with _ | _
      · simp [step, hT, ho, hio, hc']
      · simp [step, hT, ho, hio, setCS]

theorem rel_clear {I : LockImpl} (hR : ReleaseFrees I) (evs : List Event) (pid t : Nat)
    (hT : (replay I evs).os.table pid = some t) :
    (replay I (evs ++ [.release pid])).cs = setCS (replay I evs).cs ⟨pid, t⟩ false := by
  funext x
  by_cases hx : x = ⟨pid, t⟩
  · subst hx
    rw [rel_q hR evs pid t hT]
    simp [setCS]
  · rw [rel_other evs pid t hT x hx]
    simp [setCS, hx]

theorem acq_none {I : LockImpl} (evs : List Event) (pid : Nat)
    (hT : (replay I evs).os.table pid = none) :
    (replay I (evs ++ [.acquire pid])).cs = (replay I evs).cs := by
  rw [replay_snoc']
  simp [step, hT]

theorem acq_some {I : LockImpl} (evs : List Event) (pid t : Nat)
    (hT : (replay I evs).os.table pid = some t)
    (hg : grants I (replay I evs) = true) :
    (replay I (evs ++ [.acquire pid])).cs = setCS (replay I evs).cs ⟨pid, t⟩ true := by
  rw [replay_snoc']
  simp [step, hT, hg]

/-- A granted acquire changes nothing when the critical section is not empty. -/
theorem acq_nonempty {I : LockImpl} (hM : Mutex I) (evs : List Event) (pid : Nat) (q : Proc)
    (hq : (replay I evs).cs q = true) :
    (replay I (evs ++ [.acquire pid])).cs = (replay I evs).cs := by
  have hM' := hM (evs ++ [.acquire pid])
  rw [replay_snoc'] at hM' ⊢
  generalize replay I evs = s at hq hM' ⊢
  rcases hT : s.os.table pid with _ | t0
  · simp [step, hT]
  · rcases hg : grants I s with _ | _
    · simp [step, hT, hg]
    · have h1 : (step I s (.acquire pid)).cs ⟨pid, t0⟩ = true := by
        simp [step, hT, hg, setCS]
      have h2 : (step I s (.acquire pid)).cs q = true := by
        simp [step, hT, hg, setCS, hq]
      have hpt : (⟨pid, t0⟩ : Proc) = q := hM' _ _ h1 h2
      subst hpt
      simp only [step, hT, hg, ↓reduceIte]
      funext x
      by_cases hx : x = ⟨pid, t0⟩
      · subst hx
        simp [setCS, hq]
      · simp [setCS, hx]

theorem exit_eq {I J : LockImpl} (evs : List Event) (pid : Nat)
    (hos : (replay I evs).os = (replay J evs).os)
    (hcs : (replay I evs).cs = (replay J evs).cs) :
    (replay I (evs ++ [.exit pid])).cs = (replay J (evs ++ [.exit pid])).cs := by
  have ht : (replay I evs).os.table pid = (replay J evs).os.table pid := by rw [hos]
  rw [replay_snoc', replay_snoc']
  rcases hT : (replay I evs).os.table pid with _ | t0 <;> simp [step, ← ht, hT, hcs]

theorem release_eq {I J : LockImpl} (hR : ReleaseFrees I) (hR' : ReleaseFrees J)
    (evs : List Event) (pid : Nat)
    (hos : (replay I evs).os = (replay J evs).os)
    (hcs : (replay I evs).cs = (replay J evs).cs) :
    (replay I (evs ++ [.release pid])).cs = (replay J (evs ++ [.release pid])).cs := by
  have ht : (replay I evs).os.table pid = (replay J evs).os.table pid := by rw [hos]
  rcases hT : (replay I evs).os.table pid with _ | t0
  · have hTJ : (replay J evs).os.table pid = none := by rw [← ht]; exact hT
    rw [rel_none evs pid hT, rel_none evs pid hTJ, hcs]
  · have hTJ : (replay J evs).os.table pid = some t0 := by rw [← ht]; exact hT
    rw [rel_clear hR evs pid t0 hT, rel_clear hR' evs pid t0 hTJ, hcs]

theorem acq_eq {I J : LockImpl} (hM : Mutex I) (hN : NoOrphanHold I)
    (hM' : Mutex J) (hN' : NoOrphanHold J)
    (evs : List Event) (pid : Nat)
    (hos : (replay I evs).os = (replay J evs).os)
    (hcs : (replay I evs).cs = (replay J evs).cs) :
    (replay I (evs ++ [.acquire pid])).cs = (replay J (evs ++ [.acquire pid])).cs := by
  have ht : (replay I evs).os.table pid = (replay J evs).os.table pid := by rw [hos]
  by_cases hC : ∃ q, (replay I evs).cs q = true
  · obtain ⟨q, hq⟩ := hC
    have hqJ : (replay J evs).cs q = true := by rw [← hcs]; exact hq
    rw [acq_nonempty hM evs pid q hq, acq_nonempty hM' evs pid q hqJ, hcs]
  · have hE : ∀ q, (replay I evs).cs q = false := by
      intro q
      cases h : (replay I evs).cs q with
      | false => rfl
      | true => exact absurd ⟨q, h⟩ hC
    have gI : grants I (replay I evs) = true := by
      cases hg : grants I (replay I evs) with
      | false =>
        obtain ⟨q, hq, _⟩ := hN evs hg
        rw [hE q] at hq
        cases hq
      | true => rfl
    have gJ : grants J (replay J evs) = true := by
      cases hg : grants J (replay J evs) with
      | false =>
        obtain ⟨q, hq, _⟩ := hN' evs hg
        have hq0 : (replay I evs).cs q = true := by rw [hcs]; exact hq
        rw [hE q] at hq0
        cases hq0
      | true => rfl
    rcases hT : (replay I evs).os.table pid with _ | t0
    · have hTJ : (replay J evs).os.table pid = none := by rw [← ht]; exact hT
      rw [acq_none evs pid hT, acq_none evs pid hTJ, hcs]
    · have hTJ : (replay J evs).os.table pid = some t0 := by rw [← ht]; exact hT
      rw [acq_some evs pid t0 hT gI, acq_some evs pid t0 hTJ gJ, hcs]

/-- The process table and the critical section agree after each event sequence. -/
theorem agree_rev (I J : LockImpl) (hI : Mutex I ∧ NoOrphanHold I ∧ ReleaseFrees I)
    (hJ : Mutex J ∧ NoOrphanHold J ∧ ReleaseFrees J) :
    ∀ r : List Event, (replay I r.reverse).os = (replay J r.reverse).os ∧
      (replay I r.reverse).cs = (replay J r.reverse).cs := by
  obtain ⟨hM, hN, hR⟩ := hI
  obtain ⟨hM', hN', hR'⟩ := hJ
  intro r
  induction r with
  | nil => exact ⟨rfl, rfl⟩
  | cons x r ih =>
    obtain ⟨hos, hcs⟩ := ih
    rw [List.reverse_cons]
    refine ⟨?_, ?_⟩
    · rw [replay_snoc', replay_snoc']
      exact step_os_eq _ _ hos x
    · cases x with
      | spawn pid => rw [cs_spawn, cs_spawn, hcs]
      | exit pid => exact exit_eq r.reverse pid hos hcs
      | acquire pid => exact acq_eq hM hN hM' hN' r.reverse pid hos hcs
      | release pid => exact release_eq hR hR' r.reverse pid hos hcs

/-- The laws are complete: two designs that pass each law put the same
processes in the critical section after each event sequence. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  obtain ⟨mI, nI, _, rI, _, _⟩ := hI
  obtain ⟨mJ, nJ, _, rJ, _, _⟩ := hJ
  have h := agree_rev I J ⟨mI, nI, rI⟩ ⟨mJ, nJ, rJ⟩ evs.reverse
  rw [List.reverse_reverse] at h
  rw [h.2]

end Complete
