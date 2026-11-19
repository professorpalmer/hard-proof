import Laws

open Laws

namespace Complete

theorem replay_snoc {I : LockImpl} (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

theorem snoc_ind (P : List Event → Prop) (h0 : P [])
    (hs : ∀ l a, P l → P (l ++ [a])) : ∀ l, P l := by
  have key : ∀ n l, l.length = n → P l := by
    intro n
    induction n with
    | zero =>
      intro l hl
      have : l = [] := List.eq_nil_of_length_eq_zero hl
      subst this; exact h0
    | succ n ih =>
      intro l hl
      rcases List.eq_nil_or_concat l with h | ⟨l', b, h⟩
      · subst h; exact h0
      · subst h
        simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hl
        have := hs l' b (ih l' (by omega))
        simpa using this
  intro l; exact key _ l rfl

theorem os_acq {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (Event.acquire pid)).os = s.os := by
  simp only [step]
  split
  · rfl
  · split <;> rfl

theorem os_rel {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (Event.release pid)).os = s.os := by
  simp only [step]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem os_step {I J : LockImpl} (s : State I) (t : State J) (e : Event)
    (h : s.os = t.os) : (step I s e).os = (step J t e).os := by
  obtain ⟨os1, o1, c1⟩ := s
  obtain ⟨os2, o2, c2⟩ := t
  simp only at h
  subst h
  cases e with
  | spawn pid => cases hpid : os1.table pid <;> simp [step, hpid]
  | exit pid => cases hpid : os1.table pid <;> simp [step, hpid]
  | acquire pid => rw [os_acq, os_acq]
  | release pid => rw [os_rel, os_rel]

theorem cs_spawn {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (Event.spawn pid)).cs = s.cs := by
  cases hpid : s.os.table pid <;> simp [step, hpid]

theorem cs_exit {I : LockImpl} (s : State I) (pid : Nat) :
    (step I s (Event.exit pid)).cs =
      match s.os.table pid with
      | none => s.cs
      | some t => setCS s.cs ⟨pid, t⟩ false := by
  cases hpid : s.os.table pid <;> simp [step, hpid]

theorem setCS_self (c : Proc → Bool) (q : Proc) (h : c q = true) : setCS c q true = c := by
  funext r; unfold setCS; by_cases hr : r = q
  · subst hr; simp [h]
  · simp [hr]

theorem setCS_self' (c : Proc → Bool) (q : Proc) (h : c q = false) : setCS c q false = c := by
  funext r; unfold setCS; by_cases hr : r = q
  · subst hr; simp [h]
  · simp [hr]

theorem acq_other {I : LockImpl} (hm : Mutex I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t) (p : Proc)
    (hp : (replay I evs).cs p = true) (hne : p ≠ ⟨pid, t⟩) :
    (replay I (evs ++ [Event.acquire pid])).cs = (replay I evs).cs := by
  by_cases hg : grants I (replay I evs) = true
  · exfalso
    have e1 : (step I (replay I evs) (Event.acquire pid)).cs =
        setCS (replay I evs).cs ⟨pid, t⟩ true := by
      simp only [step, ht, hg, ite_true]
    have := hm (evs ++ [Event.acquire pid]) p ⟨pid, t⟩
    rw [replay_snoc, e1] at this
    have h3 := this (by
      unfold setCS; simp [hne, hp]) (by
      unfold setCS; simp)
    exact hne h3
  · have hg' : grants I (replay I evs) = false := by simpa using hg
    rw [replay_snoc]
    simp only [step, ht, hg']
    simp

theorem acq_free {I : LockImpl} (hn : NoOrphanHold I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t)
    (hall : ∀ p, p ≠ ⟨pid, t⟩ → (replay I evs).cs p = false) :
    (replay I (evs ++ [Event.acquire pid])).cs = setCS (replay I evs).cs ⟨pid, t⟩ true := by
  rw [replay_snoc]
  by_cases hg : grants I (replay I evs) = true
  · simp only [step, ht, hg, ite_true]
  · have hg' : grants I (replay I evs) = false := by simpa using hg
    simp only [step, ht, hg']
    by_cases hq : (replay I evs).cs ⟨pid, t⟩ = true
    · simp [setCS_self _ _ hq]
    · exfalso
      obtain ⟨r, hr, _⟩ := hn evs hg'
      by_cases hrq : r = ⟨pid, t⟩
      · subst hrq; exact hq hr
      · rw [hall r hrq] at hr; cases hr

theorem rel_cs {I : LockImpl} (hr : ReleaseFrees I) (evs : List Event) (pid t : Nat)
    (ht : (replay I evs).os.table pid = some t) :
    (replay I (evs ++ [Event.release pid])).cs = setCS (replay I evs).cs ⟨pid, t⟩ false := by
  have key : replay I (evs ++ [Event.release pid]) = step I (replay I evs) (Event.release pid) :=
    replay_snoc evs _
  by_cases hq : (replay I evs).cs ⟨pid, t⟩ = true
  · have h := hr evs ⟨pid, t⟩ hq
    rw [key] at h ⊢
    cases hown : (replay I evs).owner with
    | none =>
      simp only [step, ht, hown] at h
      rw [hq] at h; cases h
    | some r =>
      by_cases hio : I.isOwner r ⟨pid, t⟩ = true
      · simp [step, ht, hown, hio]
      · have : I.isOwner r ⟨pid, t⟩ = false := by simpa using hio
        simp only [step, ht, hown, this] at h
        simp only [Bool.false_eq_true, ite_false] at h
        rw [hq] at h; cases h
  · have hq' : (replay I evs).cs ⟨pid, t⟩ = false := by simpa using hq
    rw [setCS_self' _ _ hq']
    rw [key]
    simp only [step, ht]
    cases hown : (replay I evs).owner with
    | none => rfl
    | some r =>
      by_cases hio : I.isOwner r ⟨pid, t⟩ = true
      · simp [hio, setCS_self' _ _ hq']
      · have : I.isOwner r ⟨pid, t⟩ = false := by simpa using hio
        simp [this]

theorem exit_cs {I : LockImpl} (evs : List Event) (pid : Nat) :
    (replay I (evs ++ [Event.exit pid])).cs =
      match (replay I evs).os.table pid with
      | none => (replay I evs).cs
      | some t => setCS (replay I evs).cs ⟨pid, t⟩ false := by
  rw [replay_snoc, cs_exit]

theorem both (I J : LockImpl) (hI : Passes I) (hJ : Passes J) : ∀ (evs : List Event),
    (replay I evs).os = (replay J evs).os ∧ (replay I evs).cs = (replay J evs).cs := by
  obtain ⟨hmI, hnI, _, hrI, _, _⟩ := hI
  obtain ⟨hmJ, hnJ, _, hrJ, _, _⟩ := hJ
  apply snoc_ind
  · exact ⟨rfl, rfl⟩
  · intro evs e ih
    obtain ⟨ho, hc⟩ := ih
    have hos : (replay I (evs ++ [e])).os = (replay J (evs ++ [e])).os := by
      rw [replay_snoc, replay_snoc]; exact os_step _ _ e ho
    refine ⟨hos, ?_⟩
    cases e with
    | spawn pid => rw [replay_snoc, replay_snoc, cs_spawn, cs_spawn, hc]
    | exit pid =>
      rw [exit_cs, exit_cs, hc, ho]
    | acquire pid =>
      cases ht : (replay I evs).os.table pid with
      | none =>
        have htJ : (replay J evs).os.table pid = none := by rw [← ho]; exact ht
        rw [replay_snoc, replay_snoc]
        simp only [step, ht, htJ]; exact hc
      | some t =>
        have htJ : (replay J evs).os.table pid = some t := by rw [← ho]; exact ht
        by_cases hex : ∃ p : Proc, p ≠ ⟨pid, t⟩ ∧ (replay I evs).cs p = true
        · obtain ⟨p, hp, hpc⟩ := hex
          rw [acq_other hmI evs pid t ht p hpc hp,
              acq_other hmJ evs pid t htJ p (by rw [← hc]; exact hpc) hp, hc]
        · have hall : ∀ p, p ≠ ⟨pid, t⟩ → (replay I evs).cs p = false := by
            intro p hp
            by_cases h : (replay I evs).cs p = true
            · exact absurd ⟨p, hp, h⟩ hex
            · simpa using h
          rw [acq_free hnI evs pid t ht hall,
              acq_free hnJ evs pid t htJ (by intro p hp; rw [← hc]; exact hall p hp), hc]
    | release pid =>
      cases ht : (replay I evs).os.table pid with
      | none =>
        have htJ : (replay J evs).os.table pid = none := by rw [← ho]; exact ht
        rw [replay_snoc, replay_snoc]
        simp only [step, ht, htJ]; exact hc
      | some t =>
        have htJ : (replay J evs).os.table pid = some t := by rw [← ho]; exact ht
        rw [rel_cs hrI evs pid t ht, rel_cs hrJ evs pid t htJ, hc]

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  rw [(both I J hI hJ evs).2]

end Complete
