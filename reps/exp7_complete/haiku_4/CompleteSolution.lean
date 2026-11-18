import Laws

open Laws

namespace Complete

/-- The OS part of a step. It does not depend on the lock design. -/
def osStep (o : OS) : Event → OS
  | .spawn pid =>
    match o.table pid with
    | some _ => o
    | none => { table := setTable o.table pid (some o.next), next := o.next + 1 }
  | .exit pid =>
    match o.table pid with
    | none => o
    | some _ => { o with table := setTable o.table pid none }
  | .acquire _ => o
  | .release _ => o

theorem step_os {I : LockImpl} (s : State I) (e : Event) :
    (step I s e).os = osStep s.os e := by
  cases e with
  | spawn pid => cases htab : s.os.table pid <;> simp [step, osStep, htab]
  | exit pid => cases htab : s.os.table pid <;> simp [step, osStep, htab]
  | acquire pid =>
    cases htab : s.os.table pid with
    | none => simp [step, osStep, htab]
    | some t =>
      simp only [step, htab, osStep]
      split <;> rfl
  | release pid =>
    cases htab : s.os.table pid with
    | none => simp [step, osStep, htab]
    | some t =>
      simp only [step, htab, osStep]
      split <;> (try split) <;> rfl

theorem replay_snoc' {I : LockImpl} (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

theorem setCS_self (c : Proc → Bool) (x : Proc) (h : c x = true) :
    setCS c x true = c := by
  funext q
  unfold setCS
  split
  · rename_i hq
    rw [hq]; exact h.symm
  · rfl

theorem setCS_false_self (c : Proc → Bool) (x : Proc) (h : c x = false) :
    setCS c x false = c := by
  funext q
  unfold setCS
  split
  · rename_i hq
    rw [hq]; exact h.symm
  · rfl

theorem spawn_cs {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (.spawn pid)).cs = s.cs := by
  cases htab : s.os.table pid <;> simp [step, htab]

theorem exit_cs_eq {I J : LockImpl} (s : State I) (s' : State J)
    (hos : s.os = s'.os) (hcs : s.cs = s'.cs) (pid : Nat) :
    (step I s (.exit pid)).cs = (step J s' (.exit pid)).cs := by
  cases htab : s.os.table pid with
  | none =>
    have htab' : s'.os.table pid = none := by rw [← hos]; exact htab
    simp [step, htab, htab', hcs]
  | some t =>
    have htab' : s'.os.table pid = some t := by rw [← hos]; exact htab
    simp [step, htab, htab', hcs]

/-- A granted acquire sets the critical section for the requester. A refused
acquire leaves it. The two designs agree when the grant decisions agree. -/
theorem acq_cs_eq {I J : LockImpl} (s : State I) (s' : State J)
    (hos : s.os = s'.os) (hcs : s.cs = s'.cs)
    (g1 : (∀ q, s.cs q = false) → grants I s = true)
    (g2 : ∀ p x : Proc, s.cs p = true → s.os.table x.pid = some x.tok → x ≠ p →
      grants I s = false)
    (g1' : (∀ q, s'.cs q = false) → grants J s' = true)
    (g2' : ∀ p x : Proc, s'.cs p = true → s'.os.table x.pid = some x.tok → x ≠ p →
      grants J s' = false)
    (pid : Nat) :
    (step I s (.acquire pid)).cs = (step J s' (.acquire pid)).cs := by
  cases htab : s.os.table pid with
  | none =>
    have htab' : s'.os.table pid = none := by rw [← hos]; exact htab
    simp [step, htab, htab', hcs]
  | some t =>
    have htab' : s'.os.table pid = some t := by rw [← hos]; exact htab
    have eI : (step I s (.acquire pid)).cs
        = if grants I s = true then setCS s.cs ⟨pid, t⟩ true else s.cs := by
      simp only [step, htab]
      split <;> rfl
    have eJ : (step J s' (.acquire pid)).cs
        = if grants J s' = true then setCS s'.cs ⟨pid, t⟩ true else s'.cs := by
      simp only [step, htab']
      split <;> rfl
    rw [eI, eJ, hcs]
    by_cases hx : s'.cs ⟨pid, t⟩ = true
    · simp only [setCS_self _ _ hx, ite_self]
    · by_cases hp : ∃ p, s'.cs p = true
      · obtain ⟨p, hp⟩ := hp
        have hne : (⟨pid, t⟩ : Proc) ≠ p := by
          intro h; subst h; exact hx hp
        have hg : grants I s = false :=
          g2 p ⟨pid, t⟩ (by rw [hcs]; exact hp) htab hne
        have hg' : grants J s' = false := g2' p ⟨pid, t⟩ hp htab' hne
        simp [hg, hg']
      · have hall' : ∀ q, s'.cs q = false := fun q => by
          cases h : s'.cs q with
          | false => rfl
          | true => exact absurd ⟨q, h⟩ hp
        have hall : ∀ q, s.cs q = false := fun q => by rw [hcs]; exact hall' q
        have hg : grants I s = true := g1 hall
        have hg' : grants J s' = true := g1' hall'
        simp [hg, hg']

/-- The release shape: a release either leaves the critical section alone or
clears the releasing process. -/
theorem rel_cases {I : LockImpl} (s : State I) (pid t : Nat)
    (htab : s.os.table pid = some t) :
    (step I s (.release pid)).cs = s.cs ∨
      (step I s (.release pid)).cs = setCS s.cs ⟨pid, t⟩ false := by
  cases ho : s.owner with
  | none => left; simp [step, htab, ho]
  | some r =>
    by_cases hio : I.isOwner r ⟨pid, t⟩ = true
    · right; simp [step, htab, ho, hio]
    · left; simp [step, htab, ho, hio]

theorem rel_shape {I : LockImpl} (s : State I) (pid t : Nat)
    (htab : s.os.table pid = some t)
    (rf : ∀ p : Proc, s.cs p = true → (step I s (.release p.pid)).cs p = false) :
    (step I s (.release pid)).cs = setCS s.cs ⟨pid, t⟩ false := by
  rcases rel_cases s pid t htab with h | h
  · have hx : s.cs ⟨pid, t⟩ = false := by
      cases hc : s.cs ⟨pid, t⟩ with
      | false => rfl
      | true =>
        have this := rf ⟨pid, t⟩ hc
        change (step I s (.release pid)).cs ⟨pid, t⟩ = false at this
        rw [h, hc] at this
        cases this
    rw [h]
    exact (setCS_false_self _ _ hx).symm
  · exact h

theorem rel_cs_eq {I J : LockImpl} (s : State I) (s' : State J)
    (hos : s.os = s'.os) (hcs : s.cs = s'.cs)
    (rf : ∀ p : Proc, s.cs p = true → (step I s (.release p.pid)).cs p = false)
    (rf' : ∀ p : Proc, s'.cs p = true → (step J s' (.release p.pid)).cs p = false)
    (pid : Nat) :
    (step I s (.release pid)).cs = (step J s' (.release pid)).cs := by
  cases htab : s.os.table pid with
  | none =>
    have htab' : s'.os.table pid = none := by rw [← hos]; exact htab
    simp [step, htab, htab', hcs]
  | some t =>
    have htab' : s'.os.table pid = some t := by rw [← hos]; exact htab
    rw [rel_shape s pid t htab rf, rel_shape s' pid t htab' rf', hcs]

/-- Law 2 gives a grant when no process is in the critical section. -/
theorem g1_of {I : LockImpl} (hN : NoOrphanHold I) (pre : List Event) :
    (∀ q, (replay I pre).cs q = false) → grants I (replay I pre) = true := by
  intro hall
  cases hg : grants I (replay I pre) with
  | true => rfl
  | false =>
    obtain ⟨q, hq, _⟩ := hN pre hg
    rw [hall q] at hq
    cases hq

/-- Laws 1 and 3 refuse every other live process while one process is inside. -/
theorem g2_of {I : LockImpl} (hM : Mutex I) (hH : HolderKeepsLock I)
    (pre : List Event) (p x : Proc) (hp : (replay I pre).cs p = true)
    (hx : (replay I pre).os.table x.pid = some x.tok) (hne : x ≠ p) :
    grants I (replay I pre) = false := by
  cases hg : grants I (replay I pre) with
  | false => rfl
  | true =>
    exfalso
    have hcsx : (replay I (pre ++ [Event.acquire x.pid])).cs x = true := by
      rw [replay_snoc']
      simp [step, hx, hg, setCS]
    have hp' : (replay I (pre ++ [Event.acquire x.pid])).cs p = true :=
      (hH pre (.acquire x.pid) p hp (by intro h; cases h) (by intro h; cases h)).2
    exact hne (hM (pre ++ [Event.acquire x.pid]) p x hp' hcsx).symm

/-- Law 4 gives the release shape for each reachable state. -/
theorem rf_of {I : LockImpl} (hR : ReleaseFrees I) (pre : List Event) :
    ∀ p : Proc, (replay I pre).cs p = true →
      (step I (replay I pre) (.release p.pid)).cs p = false := by
  intro p hp
  have h := hR pre p hp
  rw [replay_snoc'] at h
  exact h

theorem step_cs_eq {I J : LockImpl} (hI : Passes I) (hJ : Passes J)
    (pre pre' : List Event) (e : Event)
    (hos : (replay I pre).os = (replay J pre').os)
    (hcs : (replay I pre).cs = (replay J pre').cs) :
    (step I (replay I pre) e).cs = (step J (replay J pre') e).cs := by
  cases e with
  | spawn pid => rw [spawn_cs, spawn_cs]; exact hcs
  | exit pid => exact exit_cs_eq _ _ hos hcs pid
  | acquire pid =>
    exact acq_cs_eq _ _ hos hcs (g1_of hI.2.1 pre) (g2_of hI.1 hI.2.2.1 pre)
      (g1_of hJ.2.1 pre') (g2_of hJ.1 hJ.2.2.1 pre') pid
  | release pid =>
    exact rel_cs_eq _ _ hos hcs (rf_of hI.2.2.2.1 pre) (rf_of hJ.2.2.2.1 pre') pid

/-- Two designs that pass each law keep the same os and critical section
along any event list. -/
theorem trace_eq {I J : LockImpl} (hI : Passes I) (hJ : Passes J) :
    ∀ (evs : List Event) (s : State I) (s' : State J),
      (∃ pre, s = replay I pre) → (∃ pre, s' = replay J pre) →
      s.os = s'.os → s.cs = s'.cs →
      (evs.foldl (step I) s).os = (evs.foldl (step J) s').os ∧
      (evs.foldl (step I) s).cs = (evs.foldl (step J) s').cs := by
  intro evs
  induction evs with
  | nil => intro s s' _ _ hos hcs; exact ⟨hos, hcs⟩
  | cons e es ih =>
    intro s s' hr hr' hos hcs
    obtain ⟨pre, rfl⟩ := hr
    obtain ⟨pre', rfl⟩ := hr'
    simp only [List.foldl_cons]
    apply ih
    · exact ⟨pre ++ [e], (replay_snoc' pre e).symm⟩
    · exact ⟨pre' ++ [e], (replay_snoc' pre' e).symm⟩
    · rw [step_os, step_os, hos]
    · exact step_cs_eq hI hJ pre pre' e hos hcs

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  have h := (trace_eq hI hJ evs (init I) (init J) ⟨[], rfl⟩ ⟨[], rfl⟩ rfl rfl).2
  exact congrFun h p

end Complete
