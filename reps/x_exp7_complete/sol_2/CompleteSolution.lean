import Laws

open Laws

namespace Complete

private def osStep (os : OS) : Event → OS
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

private theorem step_os {I : LockImpl} (s : State I) (e : Event) :
    (step I s e).os = osStep s.os e := by
  cases e with
  | spawn pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | exit pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | acquire pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some tok => cases g : grants I s <;> simp [step, osStep, h, g]
  | release pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some tok =>
      cases o : s.owner with
      | none => simp [step, osStep, h, o]
      | some r => cases w : I.isOwner r ⟨pid, tok⟩ <;> simp [step, osStep, h, o, w]

private theorem step_os_eq {I J : LockImpl} (s : State I) (t : State J)
    (h : s.os = t.os) (e : Event) : (step I s e).os = (step J t e).os := by
  rw [step_os, step_os, h]

private theorem foldl_os_eq {I J : LockImpl} (evs : List Event)
    (s : State I) (t : State J) (h : s.os = t.os) :
    (evs.foldl (step I) s).os = (evs.foldl (step J) t).os := by
  induction evs generalizing s t with
  | nil => exact h
  | cons e evs ih =>
    exact ih (step I s e) (step J t e) (step_os_eq s t h e)

private theorem replay_os_eq (I J : LockImpl) (evs : List Event) :
    (replay I evs).os = (replay J evs).os := by
  exact foldl_os_eq evs (init I) (init J) rfl

private theorem replay_snoc (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

private theorem release_keeps_false {I : LockImpl} (s : State I) (pid : Nat)
    (p : Proc) (h : s.cs p = false) : (step I s (.release pid)).cs p = false := by
  cases ht : s.os.table pid with
  | none => simp [step, ht, h]
  | some tok =>
    cases ho : s.owner with
    | none => simp [step, ht, ho, h]
    | some r =>
      cases hw : I.isOwner r ⟨pid, tok⟩ <;> simp [step, ht, ho, hw, setCS, h]

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs
  induction hrev : evs.reverse generalizing evs with
  | nil =>
    intro p
    have : evs = [] := by
      simpa using congrArg List.reverse hrev
    subst evs
    rfl
  | cons e revs ih =>
    have hev : evs = revs.reverse ++ [e] := by
      have := congrArg List.reverse hrev
      simpa using this
    subst evs
    let pre := revs.reverse
    have ihp := ih pre (by simp [pre])
    intro p
    have old := ihp p
    have hos := replay_os_eq I J pre
    rcases hI with ⟨mutexI, orphanI, keepsI, freesI, refuseI, enterI⟩
    rcases hJ with ⟨mutexJ, orphanJ, keepsJ, freesJ, refuseJ, enterJ⟩
    rw [replay_snoc, replay_snoc]
    change (step I (replay I pre) e).cs p = (step J (replay J pre) e).cs p
    cases e with
    | spawn pid =>
      simp only [step]
      rw [hos]
      split <;> exact old
    | exit pid =>
      simp only [step]
      rw [hos]
      split
      · exact old
      · simp only [setCS]
        split <;> simp_all
    | release pid =>
      by_cases hp : (replay I pre).cs p = true
      · have hpJ : (replay J pre).cs p = true := by simpa [old] using hp
        by_cases hid : pid = p.pid
        · subst pid
          simpa [replay_snoc] using Eq.trans (freesI pre p hp) (freesJ pre p hpJ).symm
        · have hki := (keepsI pre (.release pid) p hp (by simp [hid]) (by simp))
          have hkj := (keepsJ pre (.release pid) p hpJ (by simp [hid]) (by simp))
          simpa [replay_snoc] using Eq.trans hki.2 hkj.2.symm
      · have hpJ : (replay J pre).cs p = false := by
          rw [← old]
          cases h : (replay I pre).cs p with
          | false => rfl
          | true => exact False.elim (hp h)
        exact (release_keeps_false (replay I pre) pid p (by simpa using hp)).trans
          (release_keeps_false (replay J pre) pid p hpJ).symm
    | acquire pid =>
      by_cases hp : (replay I pre).cs p = true
      · have hpJ : (replay J pre).cs p = true := by simpa [old] using hp
        have hki := keepsI pre (.acquire pid) p hp (by simp) (by simp)
        have hkj := keepsJ pre (.acquire pid) p hpJ (by simp) (by simp)
        simpa [replay_snoc] using Eq.trans hki.2 hkj.2.symm
      · have hpJ : (replay J pre).cs p = false := by
          rw [← old]
          cases h : (replay I pre).cs p with
          | false => rfl
          | true => exact False.elim (hp h)
        have hpI : (replay I pre).cs p = false := old.trans hpJ
        -- It remains to compare whether the acquire newly inserts `p`.
        simp only [step]
        rw [hos]
        split
        · exact old
        · rename_i t htable
          have htableI : (replay I pre).os.table pid = some t := by
            rw [hos]
            exact htable
          by_cases hgI : grants I (replay I pre) = true
          · simp only [hgI, ↓reduceIte, setCS]
            by_cases heq : p = ⟨pid, t⟩
            · subst p
              simp only [↓reduceIte]
              by_cases hgJ : grants J (replay J pre) = true
              · simp [hgJ, setCS]
              · have := orphanJ pre (by simpa using hgJ)
                obtain ⟨q, hq, _⟩ := this
                have hqI : (replay I pre).cs q = true := by
                  rw [ihp q]
                  exact hq
                have hk := (keepsI pre (.acquire pid) q hqI (by simp) (by simp)).2
                have hnew : (replay I (pre ++ [.acquire pid])).cs (⟨pid, t⟩ : Proc) = true := by
                  simp [replay_snoc, step, htableI, hgI, setCS]
                have hqp := mutexI (pre ++ [.acquire pid]) q ⟨pid, t⟩ hk hnew
                subst q
                simpa [hgJ] using hq.symm
            · simp only [heq, ↓reduceIte, hp]
              by_cases hgJ : grants J (replay J pre) = true
              · simp [hgJ, setCS, heq, hpJ]
              · simp [hgJ, hpJ]
          · have hgIf : grants I (replay I pre) = false := by
              cases h : grants I (replay I pre) <;> simp_all
            obtain ⟨q, hqI, _⟩ := orphanI pre hgIf
            have hqJ : (replay J pre).cs q = true := by
              rw [← ihp q]
              exact hqI
            have hkJ := (keepsJ pre (.acquire pid) q hqJ (by simp) (by simp)).2
            have hpostJ : (replay J (pre ++ [.acquire pid])).cs p = false := by
              cases hj : (replay J (pre ++ [.acquire pid])).cs p with
              | false => rfl
              | true =>
                have hqp := mutexJ (pre ++ [.acquire pid]) q p hkJ hj
                subst q
                exact absurd hqJ (by simpa [hpJ])
            have hstepJ : (step J (replay J pre) (.acquire pid)).cs p = false := by
              simpa [replay_snoc] using hpostJ
            simp only [hgIf, Bool.false_eq_true, ↓reduceIte, hpI]
            simpa only [step, htable] using hstepJ.symm

end Complete
