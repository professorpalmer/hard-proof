import Laws

open Laws

namespace Complete

theorem replay_snoc' (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

/-- Induction over a trace, one event at a time. -/
theorem snoc_induction {P : List Event → Prop} (h0 : P [])
    (hs : ∀ (evs : List Event) (e : Event), P evs → P (evs ++ [e])) :
    ∀ evs : List Event, P evs := by
  have rev : ∀ xs : List Event, P xs.reverse := by
    intro xs
    induction xs with
    | nil => exact h0
    | cons e xs ih =>
      rw [List.reverse_cons]
      exact hs xs.reverse e ih
  intro evs
  have h := rev evs.reverse
  rw [List.reverse_reverse] at h
  exact h

theorem acquire_os {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (.acquire pid)).os = s.os := by
  rcases h : s.os.table pid with _ | t
  · simp [step, h]
  · simp only [step, h]
    split
    · rfl
    · rfl

theorem release_os {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (.release pid)).os = s.os := by
  rcases h : s.os.table pid with _ | t
  · simp [step, h]
  · rcases ho : s.owner with _ | r
    · simp [step, h, ho]
    · by_cases hO : I.isOwner r ⟨pid, t⟩ = true
      · simp [step, h, ho, hO]
      · simp [step, h, ho, hO]

theorem acquire_none {I : LockImpl} (s : State I) (pid : Nat)
    (h : s.os.table pid = none) : (step I s (.acquire pid)).cs = s.cs := by
  simp [step, h]

theorem release_none {I : LockImpl} (s : State I) (pid : Nat)
    (h : s.os.table pid = none) : (step I s (.release pid)).cs = s.cs := by
  simp [step, h]

/-- A release of a live process either leaves the critical section unchanged
or clears the releasing process. -/
theorem release_cases {I : LockImpl} (s : State I) (pid t : Nat)
    (ht : s.os.table pid = some t) :
    (step I s (.release pid)).cs = s.cs ∨
      (step I s (.release pid)).cs = setCS s.cs ⟨pid, t⟩ false := by
  rcases ho : s.owner with _ | r
  · left; simp [step, ht, ho]
  · by_cases hO : I.isOwner r ⟨pid, t⟩ = true
    · right; simp [step, ht, ho, hO]
    · left; simp [step, ht, ho, hO]

/-- An acquire when the critical section is empty: the lock grants. -/
theorem acquire_empty (I : LockImpl) (hI : Passes I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t)
    (hE : ∀ x : Proc, (replay I evs).cs x = false) :
    (step I (replay I evs) (.acquire pid)).cs = setCS (replay I evs).cs ⟨pid, t⟩ true := by
  have hg : grants I (replay I evs) = true := by
    cases hgr : grants I (replay I evs) with
    | true => rfl
    | false =>
      obtain ⟨q, hq, _⟩ := hI.2.1 evs hgr
      rw [hE q] at hq
      cases hq
  simp [step, ht, hg]

/-- An acquire when the critical section is not empty: the set does not change. -/
theorem acquire_nonempty (I : LockImpl) (hI : Passes I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t)
    (hne : ∃ x : Proc, (replay I evs).cs x = true) :
    (step I (replay I evs) (.acquire pid)).cs = (replay I evs).cs := by
  obtain ⟨p, hp⟩ := hne
  rcases hg : grants I (replay I evs) with _ | _
  · simp [step, ht, hg]
  · have hnew : (step I (replay I evs) (.acquire pid)).cs
        = setCS (replay I evs).cs ⟨pid, t⟩ true := by
      simp [step, ht, hg]
    have hmut : ∀ y : Proc, (replay I evs).cs y = true → y = ⟨pid, t⟩ := by
      intro y hy
      apply hI.1 (evs ++ [.acquire pid]) y ⟨pid, t⟩
      · rw [replay_snoc', hnew]
        by_cases hyq : y = ⟨pid, t⟩
        · simp [setCS, hyq]
        · simp [setCS, hyq, hy]
      · rw [replay_snoc', hnew]
        simp [setCS]
    have hpq := hmut p hp
    rw [hpq] at hp
    rw [hnew]
    funext x
    by_cases hx : x = ⟨pid, t⟩
    · rw [hx]
      simp [setCS, hp]
    · simp [setCS, hx]

/-- A release of a live process: the critical section loses that process. -/
theorem release_cs (I : LockImpl) (hI : Passes I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t) :
    (step I (replay I evs) (.release pid)).cs = setCS (replay I evs).cs ⟨pid, t⟩ false := by
  have hcases := release_cases (replay I evs) pid t ht
  by_cases hc : (replay I evs).cs ⟨pid, t⟩ = true
  · have h4 : (step I (replay I evs) (.release pid)).cs ⟨pid, t⟩ = false := by
      have := hI.2.2.2.1 evs ⟨pid, t⟩ hc
      rw [replay_snoc'] at this
      exact this
    rcases hcases with h | h
    · rw [h, hc] at h4
      cases h4
    · exact h
  · have hc' : (replay I evs).cs ⟨pid, t⟩ = false := by
      simpa using hc
    rcases hcases with h | h
    · rw [h]
      funext y
      by_cases hy : y = ⟨pid, t⟩
      · rw [hy]
        simp [setCS, hc']
      · simp [setCS, hy]
    · exact h

/-- Two designs that agree on the OS and the critical section agree after one
more event. -/
theorem snoc_step_agree (I J : LockImpl) (hI : Passes I) (hJ : Passes J)
    (evs : List Event) (e : Event)
    (hos : (replay I evs).os = (replay J evs).os)
    (hcs : (replay I evs).cs = (replay J evs).cs) :
    (step I (replay I evs) e).os = (step J (replay J evs) e).os ∧
      (step I (replay I evs) e).cs = (step J (replay J evs) e).cs := by
  cases e with
  | spawn pid =>
    rcases h : (replay I evs).os.table pid with _ | t
    · have h' : (replay J evs).os.table pid = none := by rw [← hos]; exact h
      simp [step, h', hos, hcs]
    · have h' : (replay J evs).os.table pid = some t := by rw [← hos]; exact h
      have e1 : step I (replay I evs) (.spawn pid) = replay I evs := by simp [step, h]
      have e2 : step J (replay J evs) (.spawn pid) = replay J evs := by simp [step, h']
      rw [e1, e2]
      exact ⟨hos, hcs⟩
  | exit pid =>
    rcases h : (replay I evs).os.table pid with _ | t
    · have h' : (replay J evs).os.table pid = none := by rw [← hos]; exact h
      have e1 : step I (replay I evs) (.exit pid) = replay I evs := by simp [step, h]
      have e2 : step J (replay J evs) (.exit pid) = replay J evs := by simp [step, h']
      rw [e1, e2]
      exact ⟨hos, hcs⟩
    · have h' : (replay J evs).os.table pid = some t := by rw [← hos]; exact h
      simp [step, h', hos, hcs]
  | acquire pid =>
    refine ⟨?_, ?_⟩
    · rw [acquire_os, acquire_os]; exact hos
    · rcases h : (replay I evs).os.table pid with _ | t
      · have h' : (replay J evs).os.table pid = none := by rw [← hos]; exact h
        rw [acquire_none _ pid h, acquire_none _ pid h', hcs]
      · have h' : (replay J evs).os.table pid = some t := by rw [← hos]; exact h
        by_cases hE : ∀ x : Proc, (replay I evs).cs x = false
        · have hE' : ∀ x : Proc, (replay J evs).cs x = false := by
            intro x; rw [← hcs]; exact hE x
          rw [acquire_empty I hI evs pid t h hE, acquire_empty J hJ evs pid t h' hE', hcs]
        · have hne : ∃ x : Proc, (replay I evs).cs x = true := by
            refine Classical.byContradiction fun hc => ?_
            apply hE
            intro x
            cases hx : (replay I evs).cs x with
            | false => rfl
            | true => exact absurd ⟨x, hx⟩ hc
          have hne' : ∃ x : Proc, (replay J evs).cs x = true := by
            rw [← hcs]; exact hne
          rw [acquire_nonempty I hI evs pid t h hne,
            acquire_nonempty J hJ evs pid t h' hne', hcs]
  | release pid =>
    refine ⟨?_, ?_⟩
    · rw [release_os, release_os]; exact hos
    · rcases h : (replay I evs).os.table pid with _ | t
      · have h' : (replay J evs).os.table pid = none := by rw [← hos]; exact h
        rw [release_none _ pid h, release_none _ pid h', hcs]
      · have h' : (replay J evs).os.table pid = some t := by rw [← hos]; exact h
        rw [release_cs I hI evs pid t h, release_cs J hJ evs pid t h', hcs]

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ
  have key : ∀ evs : List Event,
      (replay I evs).os = (replay J evs).os ∧ (replay I evs).cs = (replay J evs).cs := by
    apply snoc_induction
    · simp [replay, init]
    · intro evs e ih
      obtain ⟨hos, hcs⟩ := ih
      rw [replay_snoc' I, replay_snoc' J]
      exact snoc_step_agree I J hI hJ evs e hos hcs
  intro evs p
  exact congrFun (key evs).2 p

end Complete
