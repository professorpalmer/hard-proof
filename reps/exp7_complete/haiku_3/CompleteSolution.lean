import Laws

open Laws

namespace Complete

theorem replay_snoc (I : LockImpl) (pre : List Event) (e : Event) :
    replay I (pre ++ [e]) = step I (replay I pre) e := by
  simp [replay, List.foldl_append]

theorem setCS_false_of {c : Proc → Bool} {p : Proc} (h : c p = false) :
    setCS c p false = c := by
  funext q
  unfold setCS
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [hq]

theorem setCS_true_of {c : Proc → Bool} {p : Proc} (h : c p = true) :
    setCS c p true = c := by
  funext q
  unfold setCS
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [hq]

/-- With no process in the critical section, the lock grants. -/
theorem grants_of_none (K : LockImpl) (hK : Passes K) (pre : List Event)
    (h : ∀ q, (replay K pre).cs q = false) : grants K (replay K pre) = true := by
  by_cases hg : grants K (replay K pre) = true
  · exact hg
  · exfalso
    obtain ⟨q, hq, -⟩ := hK.2.1 pre (by simpa using hg)
    rw [h q] at hq
    exact absurd hq (by decide)

/-- A live holder other than the requester makes the lock refuse. -/
theorem grants_of_holder (K : LockImpl) (hK : Passes K) (pre : List Event)
    (pid t : Nat) (hT : (replay K pre).os.table pid = some t) (q : Proc)
    (hq : (replay K pre).cs q = true) (hne : q ≠ ⟨pid, t⟩) :
    grants K (replay K pre) = false := by
  by_cases hg : grants K (replay K pre) = false
  · exact hg
  exfalso
  have hg' : grants K (replay K pre) = true := by simpa using hg
  have hp : (replay K (pre ++ [.acquire pid])).cs ⟨pid, t⟩ = true := by
    rw [replay_snoc]
    simp [step, hT, hg', setCS]
  have hqq : (replay K (pre ++ [.acquire pid])).cs q = true := by
    rw [replay_snoc]
    simp [step, hT, hg', setCS, hq, hne]
  exact hne (hK.1 (pre ++ [.acquire pid]) ⟨pid, t⟩ q hp hqq).symm

theorem release_cs (K : LockImpl) (hK : ReleaseFrees K) (pre : List Event) (pid t : Nat)
    (hT : (replay K pre).os.table pid = some t) :
    (step K (replay K pre) (.release pid)).cs = setCS (replay K pre).cs ⟨pid, t⟩ false := by
  have hfree := hK pre ⟨pid, t⟩
  rw [replay_snoc] at hfree
  generalize replay K pre = s at hT hfree ⊢
  simp only [step, hT] at hfree ⊢
  by_cases hc : s.cs ⟨pid, t⟩ = true
  · cases hO : s.owner with
    | none => simp [hO, hc] at hfree
    | some r =>
      by_cases hr : K.isOwner r ⟨pid, t⟩ = true
      · simp [hO, hr]
      · simp [hO, hr, hc] at hfree
  · have hc' : s.cs ⟨pid, t⟩ = false := by simpa using hc
    cases hO : s.owner with
    | none => simp [setCS_false_of hc']
    | some r =>
      by_cases hr : K.isOwner r ⟨pid, t⟩ = true
      · simp [hr, setCS_false_of hc']
      · simp [hr, setCS_false_of hc']

/-- A release never changes the `os` part of the state. -/
theorem release_os (K : LockImpl) (s : State K) (pid : Nat) :
    (step K s (.release pid)).os = s.os := by
  cases hT : s.os.table pid <;> cases hO : s.owner <;>
    simp only [step, hT, hO] <;> (try split) <;> rfl

theorem acquire_cs (I J : LockImpl) (hI : Passes I) (hJ : Passes J) (pre : List Event)
    (pid t : Nat) (hT : (replay I pre).os.table pid = some t)
    (hTJ : (replay J pre).os.table pid = some t)
    (hcs : (replay I pre).cs = (replay J pre).cs) :
    (step I (replay I pre) (.acquire pid)).cs = (step J (replay J pre) (.acquire pid)).cs := by
  by_cases hex : ∃ q, (replay I pre).cs q = true
  · obtain ⟨q, hq⟩ := hex
    by_cases hqp : q = ⟨pid, t⟩
    · subst hqp
      have hq' : (replay J pre).cs ⟨pid, t⟩ = true := by rw [← hcs]; exact hq
      cases hgI : grants I (replay I pre) <;> cases hgJ : grants J (replay J pre) <;>
        simp [step, hT, hTJ, hgI, hgJ, setCS_true_of hq', hcs]
    · have hgI : grants I (replay I pre) = false :=
        grants_of_holder I hI pre pid t hT q hq hqp
      have hq' : (replay J pre).cs q = true := by rw [← hcs]; exact hq
      have hgJ : grants J (replay J pre) = false :=
        grants_of_holder J hJ pre pid t hTJ q hq' hqp
      simp [step, hT, hTJ, hgI, hgJ, hcs]
  · have hall : ∀ q, (replay I pre).cs q = false := by
      intro q
      cases h : (replay I pre).cs q
      · rfl
      · exact absurd ⟨q, h⟩ hex
    have hallJ : ∀ q, (replay J pre).cs q = false := by
      intro q; rw [← hcs]; exact hall q
    have hgI := grants_of_none I hI pre hall
    have hgJ := grants_of_none J hJ pre hallJ
    simp [step, hT, hTJ, hgI, hgJ, hcs]

/-- The induction step: one more event keeps the two designs equal in `os` and `cs`. -/
theorem step_agree (I J : LockImpl) (hI : Passes I) (hJ : Passes J) (pre : List Event)
    (e : Event)
    (ho : (replay I pre).os = (replay J pre).os) (hc : (replay I pre).cs = (replay J pre).cs) :
    (replay I (pre ++ [e])).os = (replay J (pre ++ [e])).os ∧
      (replay I (pre ++ [e])).cs = (replay J (pre ++ [e])).cs := by
  rw [replay_snoc, replay_snoc]
  cases e with
  | spawn pid =>
    cases hT : (replay I pre).os.table pid with
    | none =>
      have hTJ : (replay J pre).os.table pid = none := by rw [← ho]; exact hT
      simp [step, hT, hTJ, ho, hc]
    | some t =>
      have hTJ : (replay J pre).os.table pid = some t := by rw [← ho]; exact hT
      simp [step, hT, hTJ, ho, hc]
  | exit pid =>
    cases hT : (replay I pre).os.table pid with
    | none =>
      have hTJ : (replay J pre).os.table pid = none := by rw [← ho]; exact hT
      simp [step, hT, hTJ, ho, hc]
    | some t =>
      have hTJ : (replay J pre).os.table pid = some t := by rw [← ho]; exact hT
      simp [step, hT, hTJ, ho, hc]
  | acquire pid =>
    cases hT : (replay I pre).os.table pid with
    | none =>
      have hTJ : (replay J pre).os.table pid = none := by rw [← ho]; exact hT
      simp [step, hT, hTJ, ho, hc]
    | some t =>
      have hTJ : (replay J pre).os.table pid = some t := by rw [← ho]; exact hT
      refine ⟨?_, acquire_cs I J hI hJ pre pid t hT hTJ hc⟩
      cases hgI : grants I (replay I pre) <;> cases hgJ : grants J (replay J pre) <;>
        simp [step, hT, hTJ, hgI, hgJ, ho]
  | release pid =>
    cases hT : (replay I pre).os.table pid with
    | none =>
      have hTJ : (replay J pre).os.table pid = none := by rw [← ho]; exact hT
      simp [step, hT, hTJ, ho, hc]
    | some t =>
      have hTJ : (replay J pre).os.table pid = some t := by rw [← ho]; exact hT
      refine ⟨?_, ?_⟩
      · rw [release_os, release_os, ho]
      · rw [release_cs I hI.2.2.2.1 pre pid t hT, release_cs J hJ.2.2.2.1 pre pid t hTJ, hc]

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  have all : ∀ rs : List Event,
      (replay I rs.reverse).os = (replay J rs.reverse).os ∧
        (replay I rs.reverse).cs = (replay J rs.reverse).cs := by
    intro rs
    induction rs with
    | nil => simp [replay, init]
    | cons e rs ih =>
      rw [List.reverse_cons]
      exact step_agree I J hI hJ rs.reverse e ih.1 ih.2
  have key := all evs.reverse
  rw [List.reverse_reverse] at key
  rw [(key).2]

end Complete
