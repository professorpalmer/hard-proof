import Laws

open Laws

namespace Complete

theorem snoc_eq (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

def osF (os : OS) : Event → OS
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

theorem step_os (I : LockImpl) (s : State I) (e : Event) : (step I s e).os = osF s.os e := by
  cases e with
  | spawn pid => cases h : s.os.table pid <;> simp [step, osF, h]
  | exit pid => cases h : s.os.table pid <;> simp [step, osF, h]
  | acquire pid =>
    cases h : s.os.table pid with
    | none => simp [step, osF, h]
    | some t => simp only [step, osF, h]; split <;> rfl
  | release pid =>
    cases h : s.os.table pid with
    | none => simp [step, osF, h]
    | some t =>
      cases ho : s.owner with
      | none => simp [step, osF, h, ho]
      | some r =>
        by_cases hio : I.isOwner r ⟨pid, t⟩ = true <;> simp [step, osF, h, ho, hio]

theorem rev_ind (P : List Event → Prop) (h0 : P []) (hs : ∀ evs e, P evs → P (evs ++ [e])) :
    ∀ evs, P evs := by
  have : ∀ l : List Event, P l.reverse := by
    intro l
    induction l with
    | nil => exact h0
    | cons e es ih => simpa using hs _ e ih
  intro evs
  simpa using this evs.reverse

theorem os_same (I J : LockImpl) (evs : List Event) :
    (replay I evs).os = (replay J evs).os := by
  induction evs using rev_ind with
  | h0 => rfl
  | hs evs e ih =>
    rw [snoc_eq, snoc_eq, step_os, step_os, ih]

theorem acq_some (I : LockImpl) (hp : Passes I) (evs : List Event) (pid : Nat) (q : Proc)
    (hq : (replay I evs).cs q = true) :
    (step I (replay I evs) (Event.acquire pid)).cs = (replay I evs).cs := by
  obtain ⟨hm, -, h3, -, -, -⟩ := hp
  cases ht : (replay I evs).os.table pid with
  | none => simp [step, ht]
  | some t =>
    by_cases hg : grants I (replay I evs) = true
    · have hnew : (step I (replay I evs) (Event.acquire pid)).cs
          = setCS (replay I evs).cs ⟨pid, t⟩ true := by
        simp [step, ht, hg]
      rw [hnew]
      have k := h3 evs (Event.acquire pid) q hq (by simp) (by simp)
      rw [snoc_eq] at k
      have k1 := k.2
      have k2 : (step I (replay I evs) (Event.acquire pid)).cs ⟨pid, t⟩ = true := by
        rw [hnew]; simp [setCS]
      have hmm := hm (evs ++ [Event.acquire pid]) q ⟨pid, t⟩
      rw [snoc_eq] at hmm
      have heq := hmm k1 k2
      subst heq
      funext r
      simp only [setCS]
      split
      · rename_i h; rw [h]; exact hq.symm
      · rfl
    · have hg' : grants I (replay I evs) = false := by simpa using hg
      simp [step, ht, hg']

theorem rel_cs (K : LockImpl) (hK : Passes K) (evs : List Event) (pid t : Nat)
    (ht : (replay K evs).os.table pid = some t) :
    (step K (replay K evs) (Event.release pid)).cs
      = setCS (replay K evs).cs ⟨pid, t⟩ false := by
  funext r
  by_cases hr : r = ⟨pid, t⟩
  · subst hr
    by_cases hc : (replay K evs).cs ⟨pid, t⟩ = true
    · have := hK.2.2.2.1 evs ⟨pid, t⟩ hc
      rw [snoc_eq] at this
      simpa [setCS] using this
    · have hc' : (replay K evs).cs ⟨pid, t⟩ = false := by simpa using hc
      cases ho : (replay K evs).owner with
      | none => simp [step, ht, ho, setCS, hc']
      | some r0 =>
        by_cases hio : K.isOwner r0 ⟨pid, t⟩ = true <;> simp [step, ht, ho, hio, setCS, hc']
  · cases ho : (replay K evs).owner with
    | none => simp [step, ht, ho, setCS, hr]
    | some r0 =>
      by_cases hio : K.isOwner r0 ⟨pid, t⟩ = true <;> simp [step, ht, ho, hio, setCS, hr]

theorem cs_step (I J : LockImpl) (hI : Passes I) (hJ : Passes J) (evs : List Event) (e : Event)
    (hos : (replay I evs).os = (replay J evs).os)
    (hcs : ∀ p, (replay I evs).cs p = (replay J evs).cs p) :
    ∀ p, (replay I (evs ++ [e])).cs p = (replay J (evs ++ [e])).cs p := by
  rw [snoc_eq, snoc_eq]
  have hcs' : (replay I evs).cs = (replay J evs).cs := funext hcs
  intro p
  cases e with
  | spawn pid =>
    cases h1 : (replay I evs).os.table pid with
    | some t =>
      have h2 : (replay J evs).os.table pid = some t := by rw [← hos]; exact h1
      simp [step, h1, h2, hcs]
    | none =>
      have h2 : (replay J evs).os.table pid = none := by rw [← hos]; exact h1
      simp [step, h1, h2, hcs]
  | exit pid =>
    cases h1 : (replay I evs).os.table pid with
    | none =>
      have h2 : (replay J evs).os.table pid = none := by rw [← hos]; exact h1
      simp [step, h1, h2, hcs]
    | some t =>
      have h2 : (replay J evs).os.table pid = some t := by rw [← hos]; exact h1
      simp [step, h1, h2, hcs', setCS]
  | acquire pid =>
    cases h1 : (replay I evs).os.table pid with
    | none =>
      have h2 : (replay J evs).os.table pid = none := by rw [← hos]; exact h1
      simp [step, h1, h2, hcs]
    | some t =>
      have h2 : (replay J evs).os.table pid = some t := by rw [← hos]; exact h1
      by_cases hex : ∃ q, (replay I evs).cs q = true
      · obtain ⟨q, hq⟩ := hex
        have a1 := acq_some I hI evs pid q hq
        have a2 := acq_some J hJ evs pid q (by rw [← hcs]; exact hq)
        rw [a1, a2]
        exact hcs p
      · have hall : ∀ q, (replay I evs).cs q = false := by
          intro q
          cases hq : (replay I evs).cs q with
          | false => rfl
          | true => exact absurd ⟨q, hq⟩ hex
        have hallJ : ∀ q, (replay J evs).cs q = false := by
          intro q; rw [← hcs]; exact hall q
        have gI : grants I (replay I evs) = true := by
          cases hn : grants I (replay I evs) with
          | true => rfl
          | false =>
            obtain ⟨q, hq, -⟩ := hI.2.1 evs hn
            exact absurd ⟨q, hq⟩ hex
        have gJ : grants J (replay J evs) = true := by
          cases hn : grants J (replay J evs) with
          | true => rfl
          | false =>
            obtain ⟨q, hq, -⟩ := hJ.2.1 evs hn
            rw [hallJ q] at hq; cases hq
        simp [step, h1, h2, gI, gJ, setCS, hcs']
  | release pid =>
    cases h1 : (replay I evs).os.table pid with
    | none =>
      have h2 : (replay J evs).os.table pid = none := by rw [← hos]; exact h1
      simp [step, h1, h2, hcs]
    | some t =>
      have h2 : (replay J evs).os.table pid = some t := by rw [← hos]; exact h1
      rw [rel_cs I hI evs pid t h1, rel_cs J hJ evs pid t h2, hcs']

theorem both (I J : LockImpl) (hI : Passes I) (hJ : Passes J) (evs : List Event) :
    ∀ p, (replay I evs).cs p = (replay J evs).cs p := by
  induction evs using rev_ind with
  | h0 => intro p; rfl
  | hs evs e ih =>
    exact cs_step I J hI hJ evs e (os_same I J evs) ih

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  exact both I J hI hJ evs p

end Complete
