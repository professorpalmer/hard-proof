import Laws

open Laws

namespace Complete

private theorem replay_snoc {I : LockImpl} (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

private theorem step_os {I J : LockImpl} (s : State I) (t : State J)
    (h : s.os = t.os) (e : Event) : (step I s e).os = (step J t e).os := by
  cases e with
  | spawn pid =>
      cases hp : s.os.table pid <;> simp [step, hp, ← h]
  | exit pid =>
      cases hp : s.os.table pid <;> simp [step, hp, ← h]
  | acquire pid =>
      cases hp : s.os.table pid with
      | none => simp [step, hp, ← h]
      | some tok =>
          simp only [step, hp, ← h]
          split <;> split <;> simp [h]
  | release pid =>
      have hs : (step I s (.release pid)).os = s.os := by
        cases hp : s.os.table pid with
        | none => simp [step, hp]
        | some tok =>
            cases ho : s.owner with
            | none => simp [step, hp, ho]
            | some r =>
                simp only [step, hp, ho]
                split <;> rfl
      have ht : (step J t (.release pid)).os = t.os := by
        cases hp : t.os.table pid with
        | none => simp [step, hp]
        | some tok =>
            cases ho : t.owner with
            | none => simp [step, hp, ho]
            | some r =>
                simp only [step, hp, ho]
                split <;> rfl
      rw [hs, ht]
      exact h

private theorem fold_os {I J : LockImpl} (evs : List Event) (s : State I) (t : State J)
    (h : s.os = t.os) :
    (evs.foldl (step I) s).os = (evs.foldl (step J) t).os := by
  induction evs generalizing s t with
  | nil => exact h
  | cons e es ih => exact ih _ _ (step_os s t h e)

private theorem replay_os (I J : LockImpl) (evs : List Event) :
    (replay I evs).os = (replay J evs).os := by
  exact fold_os evs (init I) (init J) rfl

private theorem snoc_induction (P : List α → Prop) (hnil : P [])
    (hsnoc : ∀ xs x, P xs → P (xs ++ [x])) : ∀ xs, P xs := by
  have aux : ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil => simpa using hnil
    | cons x xs ih => simpa using hsnoc xs.reverse x ih
  intro xs
  simpa using aux xs.reverse

private theorem release_subset {I : LockImpl} (s : State I) (pid : Nat) (p : Proc) :
    (step I s (.release pid)).cs p = true → s.cs p = true := by
  intro h
  cases ht : s.os.table pid with
  | none => simpa [step, ht] using h
  | some tok =>
      cases ho : s.owner with
      | none => simpa [step, ht, ho] using h
      | some r =>
          cases hi : I.isOwner r ⟨pid, tok⟩ with
          | false => simpa [step, ht, ho, hi] using h
          | true =>
              simp only [step, ht, ho, hi, ↓reduceIte, setCS] at h
              split at h
              · contradiction
              · exact h

private theorem same_only_holder {I J : LockImpl} (evs : List Event) (p q : Proc)
    (mI : Mutex I) (mJ : Mutex J)
    (hqI : (replay I evs).cs q = true) (hqJ : (replay J evs).cs q = true) :
    (replay I evs).cs p = (replay J evs).cs p := by
  cases hpI : (replay I evs).cs p <;> cases hpJ : (replay J evs).cs p
  · rfl
  · have hpq := mJ evs p q hpJ hqJ
    subst hpq
    simp_all
  · have hpq := mI evs p q hpI hqI
    subst hpq
    simp_all
  · rfl
  
/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
  ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs
  apply snoc_induction (fun evs => ∀ p, (replay I evs).cs p = (replay J evs).cs p)
  ·
    intro p
    rfl
  · intro es e ih
    intro p
    have hos := replay_os I J es
    rcases hI with ⟨mI, nI, kI, rI, wI⟩
    rcases hJ with ⟨mJ, nJ, kJ, rJ, wJ⟩
    rw [replay_snoc, replay_snoc]
    cases e with
    | spawn pid =>
        cases htI : (replay I es).os.table pid with
        | none =>
            have htJ : (replay J es).os.table pid = none := by simpa [← hos] using htI
            simpa [step, htI, htJ] using ih p
        | some tok =>
            have htJ : (replay J es).os.table pid = some tok := by simpa [← hos] using htI
            simpa [step, htI, htJ] using ih p
    | exit pid =>
        cases htI : (replay I es).os.table pid with
        | none =>
            have htJ : (replay J es).os.table pid = none := by simpa [← hos] using htI
            simpa [step, htI, htJ] using ih p
        | some tok =>
            have htJ : (replay J es).os.table pid = some tok := by simpa [← hos] using htI
            simp only [step, htI, htJ, setCS]
            split <;> simp_all
    | acquire pid =>
        cases htI : (replay I es).os.table pid with
        | none =>
            have htJ : (replay J es).os.table pid = none := by simpa [← hos] using htI
            simpa [step, htI, htJ] using ih p
        | some tok =>
            have htJ : (replay J es).os.table pid = some tok := by simpa [← hos] using htI
            classical
            by_cases hex : ∃ q, (replay I es).cs q = true
            · obtain ⟨q, hqI⟩ := hex
              have hqJ : (replay J es).cs q = true := by simpa [ih q] using hqI
              have hqI' := (kI es (.acquire pid) q hqI nofun nofun).2
              have hqJ' := (kJ es (.acquire pid) q hqJ nofun nofun).2
              rw [← replay_snoc (I := I), ← replay_snoc (I := J)]
              exact same_only_holder (es ++ [.acquire pid]) p q mI mJ hqI' hqJ'
            · have hemptyI : ∀ q, (replay I es).cs q = false := by
                intro q
                cases hq : (replay I es).cs q
                · rfl
                · exact False.elim (hex ⟨q, hq⟩)
              have hemptyJ : ∀ q, (replay J es).cs q = false := by
                intro q
                rw [← ih q]
                exact hemptyI q
              have hgI : grants I (replay I es) = true := by
                cases hg : grants I (replay I es)
                · obtain ⟨q, hq, _⟩ := nI es hg
                  simp [hemptyI q] at hq
                · rfl
              have hgJ : grants J (replay J es) = true := by
                cases hg : grants J (replay J es)
                · obtain ⟨q, hq, _⟩ := nJ es hg
                  simp [hemptyJ q] at hq
                · rfl
              simp [step, htI, htJ, hgI, hgJ, setCS, hemptyI, hemptyJ]
    | release pid =>
        classical
        by_cases hex : ∃ q, (replay I es).cs q = true
        · obtain ⟨q, hqI⟩ := hex
          have hqJ : (replay J es).cs q = true := by simpa [ih q] using hqI
          by_cases heq : pid = q.pid
          · subst heq
            have hfreeI := rI es q hqI
            have hfreeJ := rJ es q hqJ
            rw [replay_snoc] at hfreeI hfreeJ
            cases hpI : (step I (replay I es) (.release q.pid)).cs p
            · cases hpJ : (step J (replay J es) (.release q.pid)).cs p
              · rfl
              · have hp0 := release_subset (replay J es) q.pid p hpJ
                have hpq := mJ es p q hp0 hqJ
                subst hpq
                simp_all
            · have hp0 := release_subset (replay I es) q.pid p hpI
              have hpq := mI es p q hp0 hqI
              subst hpq
              simp_all
          · have hqI' := (kI es (.release pid) q hqI (by simpa using heq) nofun).2
            have hqJ' := (kJ es (.release pid) q hqJ (by simpa using heq) nofun).2
            rw [← replay_snoc (I := I), ← replay_snoc (I := J)]
            exact same_only_holder (es ++ [.release pid]) p q mI mJ hqI' hqJ'
        · have hemptyI : ∀ q, (replay I es).cs q = false := by
            intro q
            cases hq : (replay I es).cs q
            · rfl
            · exact False.elim (hex ⟨q, hq⟩)
          have hemptyJ : ∀ q, (replay J es).cs q = false := by
            intro q
            rw [← ih q]
            exact hemptyI q
          cases hpI : (step I (replay I es) (.release pid)).cs p
          · cases hpJ : (step J (replay J es) (.release pid)).cs p
            · rfl
            · have := release_subset (replay J es) pid p hpJ
              simp [hemptyJ p] at this
          · have := release_subset (replay I es) pid p hpI
            simp [hemptyI p] at this

end Complete
