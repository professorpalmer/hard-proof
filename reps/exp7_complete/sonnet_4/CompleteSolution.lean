import Laws

open Laws

namespace Complete

theorem replay_snoc (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

theorem os_acq (I : LockImpl) (s : State I) (pid : Nat) :
    (step I s (Event.acquire pid)).os = s.os := by
  simp only [step]
  split
  · rfl
  · split <;> rfl

theorem os_rel (I : LockImpl) (s : State I) (pid : Nat) :
    (step I s (Event.release pid)).os = s.os := by
  simp only [step]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rfl

theorem os_step {I J : LockImpl} (s : State I) (t : State J) (e : Event)
    (h : s.os = t.os) : (step I s e).os = (step J t e).os := by
  cases e with
  | spawn pid => simp only [step]; rw [← h]; split <;> first | exact h | rfl
  | exit pid => simp only [step]; rw [← h]; split <;> first | exact h | rfl
  | acquire pid => rw [os_acq, os_acq, h]
  | release pid => rw [os_rel, os_rel, h]

theorem snoc_rec {P : List Event → Prop} (h0 : P [])
    (hs : ∀ evs e, P evs → P (evs ++ [e])) : ∀ evs, P evs := by
  have : ∀ r : List Event, P r.reverse := by
    intro r
    induction r with
    | nil => exact h0
    | cons e r ih => simpa using hs _ e ih
  intro evs
  simpa using this evs.reverse

theorem os_replay (I J : LockImpl) (evs : List Event) :
    (replay I evs).os = (replay J evs).os := by
  induction evs using snoc_rec with
  | h0 => rfl
  | hs evs e ih => rw [replay_snoc, replay_snoc]; exact os_step _ _ e ih

theorem rel_cs (I : LockImpl) (hr : ReleaseFrees I) (evs : List Event) (pid : Nat) (x : Proc) :
    (step I (replay I evs) (Event.release pid)).cs x =
      (match (replay I evs).os.table pid with
        | none => (replay I evs).cs x
        | some t => if x = ⟨pid, t⟩ then false else (replay I evs).cs x) := by
  have key := hr evs
  have key2 := key ⟨pid, 0⟩
  cases ht : (replay I evs).os.table pid with
  | none => simp [step, ht]
  | some t =>
    have kt := key ⟨pid, t⟩
    by_cases hx : x = ⟨pid, t⟩
    · subst hx
      by_cases hc : (replay I evs).cs ⟨pid, t⟩ = true
      · have := kt hc
        rw [replay_snoc] at this
        simpa [step, ht] using this
      · have hc' : (replay I evs).cs ⟨pid, t⟩ = false := by simpa using hc
        cases ho : (replay I evs).owner with
        | none => simp [step, ht, ho, hc']
        | some r =>
          by_cases hio : I.isOwner r ⟨pid, t⟩ = true
          · simp [step, ht, ho, hio, setCS]
          · simp [step, ht, ho, hio, hc']
    · cases ho : (replay I evs).owner with
      | none => simp [step, ht, ho, hx]
      | some r =>
        by_cases hio : I.isOwner r ⟨pid, t⟩ = true
        · simp [step, ht, ho, hio, setCS, hx]
        · simp [step, ht, ho, hio, hx]

theorem acq_none (I : LockImpl) (hn : NoOrphanHold I) (evs : List Event) (pid : Nat) (x : Proc)
    (hall : ∀ q, (replay I evs).cs q = false) :
    (step I (replay I evs) (Event.acquire pid)).cs x =
      (match (replay I evs).os.table pid with
        | none => (replay I evs).cs x
        | some t => if x = ⟨pid, t⟩ then true else (replay I evs).cs x) := by
  have hg : grants I (replay I evs) = true := by
    cases h : grants I (replay I evs)
    · obtain ⟨q, hq, _⟩ := hn evs h
      rw [hall q] at hq
      cases hq
    · rfl
  cases ht : (replay I evs).os.table pid with
  | none => simp [step, ht]
  | some t =>
    by_cases hx : x = ⟨pid, t⟩
    · subst hx; simp [step, ht, hg, setCS]
    · simp [step, ht, hg, setCS, hx]

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs
  obtain ⟨mI, nI, kI, rI, _, _⟩ := hI
  obtain ⟨mJ, nJ, kJ, rJ, _, _⟩ := hJ
  induction evs using snoc_rec with
  | h0 => intro p; rfl
  | hs evs e ih =>
    intro x
    have hos := os_replay I J evs
    have hcsfun : (replay I evs).cs = (replay J evs).cs := funext ih
    have holdI : ∀ q, (replay I evs).cs q = true → e ≠ Event.release q.pid →
        e ≠ Event.exit q.pid → ∀ y, (replay I (evs ++ [e])).cs y = decide (y = q) := by
      intro q hq h1 h2 y
      have := (kI evs e q hq h1 h2).2
      by_cases hy : y = q
      · subst hy; simp [this]
      · cases hc : (replay I (evs ++ [e])).cs y
        · simp [hy]
        · exact absurd (mI (evs ++ [e]) y q hc this) hy
    have holdJ : ∀ q, (replay J evs).cs q = true → e ≠ Event.release q.pid →
        e ≠ Event.exit q.pid → ∀ y, (replay J (evs ++ [e])).cs y = decide (y = q) := by
      intro q hq h1 h2 y
      have := (kJ evs e q hq h1 h2).2
      by_cases hy : y = q
      · subst hy; simp [this]
      · cases hc : (replay J (evs ++ [e])).cs y
        · simp [hy]
        · exact absurd (mJ (evs ++ [e]) y q hc this) hy
    cases e with
    | spawn pid =>
      rw [replay_snoc, replay_snoc]
      simp only [step]
      split <;> split <;> simp_all
    | exit pid =>
      rw [replay_snoc, replay_snoc]
      simp only [step]
      rw [hos]
      split
      · exact ih x
      · simp only [setCS, hcsfun]
    | release pid =>
      rw [replay_snoc, replay_snoc, rel_cs I rI, rel_cs J rJ, hos, hcsfun]
    | acquire pid =>
      by_cases hq : ∃ q, (replay I evs).cs q = true
      · obtain ⟨q, hq⟩ := hq
        have hq' : (replay J evs).cs q = true := by rw [← ih q]; exact hq
        have a := holdI q hq (by simp) (by simp) x
        have b := holdJ q hq' (by simp) (by simp) x
        rw [a, b]
      · have hall : ∀ q, (replay I evs).cs q = false := by
          intro q
          cases h : (replay I evs).cs q
          · rfl
          · exact absurd ⟨q, h⟩ hq
        have hallJ : ∀ q, (replay J evs).cs q = false := by
          intro q; rw [← ih q]; exact hall q
        rw [replay_snoc, replay_snoc, acq_none I nI evs pid x hall,
          acq_none J nJ evs pid x hallJ, hos, hcsfun]

end Complete
