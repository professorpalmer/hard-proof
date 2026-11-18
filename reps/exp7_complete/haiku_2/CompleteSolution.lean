import Laws

open Laws

namespace Complete

/-- The owner-table part of `step`. It does not depend on the lock design. -/
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

theorem step_os (K : LockImpl) (s : State K) (e : Event) :
    (step K s e).os = osStep s.os e := by
  cases e with
  | spawn pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | exit pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | acquire pid =>
    cases h : s.os.table pid <;> simp only [step, osStep, h] <;> split <;> rfl
  | release pid =>
    cases h : s.os.table pid <;> simp only [step, osStep, h] <;> (try split) <;> (try split) <;> rfl

theorem step_cs_spawn (K : LockImpl) (s : State K) (pid : Nat) :
    (step K s (.spawn pid)).cs = s.cs := by
  cases h : s.os.table pid <;> simp [step, h]

theorem step_cs_exit (K : LockImpl) (s : State K) (pid : Nat) :
    (step K s (.exit pid)).cs =
      (match s.os.table pid with
        | none => s.cs
        | some t => setCS s.cs ⟨pid, t⟩ false) := by
  cases h : s.os.table pid <;> simp [step, h]

theorem replay_snoc (K : LockImpl) (pre : List Event) (e : Event) :
    replay K (pre ++ [e]) = step K (replay K pre) e := by
  simp [replay, List.foldl_append]

theorem setCS_false_of (c : Proc → Bool) (p : Proc) (hc : c p = false) :
    setCS c p false = c := by
  funext x
  simp only [setCS]
  split
  · next h => subst h; exact hc.symm
  · rfl

/-- An acquire by a process while another process is in the critical section
leaves the critical section unchanged. With none in it, the requester enters. -/
theorem acq_cs (K : LockImpl) (hM : Mutex K) (hN : NoOrphanHold K) (pre : List Event)
    (pid t : Nat) (h : (replay K pre).os.table pid = some t) :
    ((∃ q, (replay K pre).cs q = true) →
      (step K (replay K pre) (.acquire pid)).cs = (replay K pre).cs) ∧
    ((¬ ∃ q, (replay K pre).cs q = true) →
      (step K (replay K pre) (.acquire pid)).cs = setCS (replay K pre).cs ⟨pid, t⟩ true) := by
  have hstep : step K (replay K pre) (.acquire pid) =
      (if grants K (replay K pre) then
        { replay K pre with owner := some (K.record ⟨pid, t⟩),
                            cs := setCS (replay K pre).cs ⟨pid, t⟩ true }
       else replay K pre) := by
    simp only [step, h]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hg : grants K (replay K pre) = true
    · have hcs' : (step K (replay K pre) (.acquire pid)).cs =
          setCS (replay K pre).cs ⟨pid, t⟩ true := by
        rw [hstep, if_pos hg]
      have hpq : (⟨pid, t⟩ : Proc) = q := by
        apply hM (pre ++ [.acquire pid]) ⟨pid, t⟩ q
        · rw [replay_snoc, hcs']
          simp [setCS]
        · rw [replay_snoc, hcs']
          by_cases hqp : q = ⟨pid, t⟩
          · simp [setCS, hqp]
          · simp [setCS, hqp, hq]
      rw [hcs']
      funext x
      simp only [setCS]
      by_cases hx : x = ⟨pid, t⟩
      · rw [if_pos hx, hx, hpq]
        exact hq.symm
      · rw [if_neg hx]
    · rw [hstep, if_neg hg]
  · intro hn
    have hg : grants K (replay K pre) = true := by
      cases hb : grants K (replay K pre)
      · obtain ⟨q, hq, -⟩ := hN pre hb
        exact absurd ⟨q, hq⟩ hn
      · rfl
    rw [hstep, if_pos hg]

/-- A release by the holder of a process clears it. A release that reaches no
holder leaves the critical section unchanged. -/
theorem rel_cs (K : LockImpl) (hR : ReleaseFrees K) (pre : List Event) (pid t : Nat)
    (h : (replay K pre).os.table pid = some t) :
    ((replay K pre).cs ⟨pid, t⟩ = false →
      (step K (replay K pre) (.release pid)).cs = (replay K pre).cs) ∧
    ((replay K pre).cs ⟨pid, t⟩ = true →
      (step K (replay K pre) (.release pid)).cs = setCS (replay K pre).cs ⟨pid, t⟩ false) := by
  have hf : (replay K pre).cs ⟨pid, t⟩ = true →
      (replay K (pre ++ [.release pid])).cs ⟨pid, t⟩ = false :=
    fun hc => hR pre ⟨pid, t⟩ hc
  rw [replay_snoc] at hf
  generalize replay K pre = s at h hf ⊢
  constructor
  · intro hc
    simp only [step, h]
    split
    · rfl
    · split
      · exact setCS_false_of s.cs ⟨pid, t⟩ hc
      · rfl
  · intro hc
    have hf' := hf hc
    cases ho : s.owner with
    | none => simp [step, h, ho, hc] at hf'
    | some r =>
      cases hiso : K.isOwner r ⟨pid, t⟩
      · simp [step, h, ho, hiso, hc] at hf'
      · simp [step, h, ho, hiso]

theorem one_step (I J : LockImpl)
    (hI : Mutex I ∧ NoOrphanHold I ∧ ReleaseFrees I)
    (hJ : Mutex J ∧ NoOrphanHold J ∧ ReleaseFrees J)
    (pre : List Event) (e : Event)
    (hos : (replay I pre).os = (replay J pre).os)
    (hcs : (replay I pre).cs = (replay J pre).cs) :
    (replay I (pre ++ [e])).os = (replay J (pre ++ [e])).os ∧
    (replay I (pre ++ [e])).cs = (replay J (pre ++ [e])).cs := by
  obtain ⟨hMI, hNI, hRI⟩ := hI
  obtain ⟨hMJ, hNJ, hRJ⟩ := hJ
  rw [replay_snoc, replay_snoc]
  refine ⟨?_, ?_⟩
  · rw [step_os, step_os, hos]
  · cases e with
    | spawn pid => rw [step_cs_spawn, step_cs_spawn, hcs]
    | exit pid => rw [step_cs_exit, step_cs_exit, hos, hcs]
    | release pid =>
      cases hT : (replay I pre).os.table pid with
      | none =>
        have hT' : (replay J pre).os.table pid = none := by rw [← hos, hT]
        simp only [step, hT, hT']
        exact hcs
      | some tt =>
        have hT' : (replay J pre).os.table pid = some tt := by rw [← hos, hT]
        by_cases hp : (replay I pre).cs ⟨pid, tt⟩ = true
        · have hp' : (replay J pre).cs ⟨pid, tt⟩ = true := by
            rw [← hcs]; exact hp
          rw [(rel_cs I hRI pre pid tt hT).2 hp, (rel_cs J hRJ pre pid tt hT').2 hp', hcs]
        · have hp0 : (replay I pre).cs ⟨pid, tt⟩ = false := by
            simpa using hp
          have hp' : (replay J pre).cs ⟨pid, tt⟩ = false := by
            rw [← hcs]; exact hp0
          rw [(rel_cs I hRI pre pid tt hT).1 hp0, (rel_cs J hRJ pre pid tt hT').1 hp', hcs]
    | acquire pid =>
      cases hT : (replay I pre).os.table pid with
      | none =>
        have hT' : (replay J pre).os.table pid = none := by rw [← hos, hT]
        simp only [step, hT, hT']
        exact hcs
      | some tt =>
        have hT' : (replay J pre).os.table pid = some tt := by rw [← hos, hT]
        by_cases h : ∃ q, (replay I pre).cs q = true
        · have h' : ∃ q, (replay J pre).cs q = true := by
            obtain ⟨q, hq⟩ := h
            exact ⟨q, by rw [← hcs]; exact hq⟩
          rw [(acq_cs I hMI hNI pre pid tt hT).1 h, (acq_cs J hMJ hNJ pre pid tt hT').1 h', hcs]
        · have h' : ¬ ∃ q, (replay J pre).cs q = true := by
            intro ⟨q, hq⟩
            exact h ⟨q, by rw [hcs]; exact hq⟩
          rw [(acq_cs I hMI hNI pre pid tt hT).2 h, (acq_cs J hMJ hNJ pre pid tt hT').2 h', hcs]

theorem chain (I J : LockImpl)
    (hI : Mutex I ∧ NoOrphanHold I ∧ ReleaseFrees I)
    (hJ : Mutex J ∧ NoOrphanHold J ∧ ReleaseFrees J) :
    ∀ (evs pre : List Event),
      (replay I pre).os = (replay J pre).os → (replay I pre).cs = (replay J pre).cs →
      (replay I (pre ++ evs)).os = (replay J (pre ++ evs)).os ∧
      (replay I (pre ++ evs)).cs = (replay J (pre ++ evs)).cs := by
  intro evs
  induction evs with
  | nil =>
    intro pre hos hcs
    simp only [List.append_nil]
    exact ⟨hos, hcs⟩
  | cons e es ih =>
    intro pre hos hcs
    have h1 := one_step I J hI hJ pre e hos hcs
    have h2 := ih (pre ++ [e]) h1.1 h1.2
    simpa [List.append_assoc] using h2

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  unfold Passes at hI hJ
  have hI' : Mutex I ∧ NoOrphanHold I ∧ ReleaseFrees I :=
    ⟨hI.1, hI.2.1, hI.2.2.2.1⟩
  have hJ' : Mutex J ∧ NoOrphanHold J ∧ ReleaseFrees J :=
    ⟨hJ.1, hJ.2.1, hJ.2.2.2.1⟩
  have key := chain I J hI' hJ' evs [] rfl rfl
  rw [List.nil_append] at key
  exact congrFun key.2 p

end Complete
