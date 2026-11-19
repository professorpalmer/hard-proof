import Laws

open Laws

namespace Complete

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ
  have replay_append : ∀ (K : LockImpl) (xs ys : List Event),
      replay K (xs ++ ys) = ys.foldl (step K) (replay K xs) := by
    intro K xs ys
    simp [replay, List.foldl_append]
  have step_os : ∀ (s : State I) (t : State J) (e : Event),
      s.os = t.os → (step I s e).os = (step J t e).os := by
    intro s t e h
    cases s with
    | mk sos so sc =>
      cases t with
      | mk tos to tc =>
        cases h
        cases e <;> cases htab : sos.table _ <;> simp [step, htab]
  have os_same : ∀ xs, (replay I xs).os = (replay J xs).os := by
    intro xs
    have aux : ∀ (rest : List Event) (s : State I) (t : State J),
        s.os = t.os →
        (rest.foldl (step I) s).os = (rest.foldl (step J) t).os := by
      intro rest
      induction rest with
      | nil => intro s t h; exact h
      | cons e es ih =>
        intro s t h
        simp only [List.foldl_cons]
        apply ih
        exact step_os s t e h
    exact aux xs (init I) (init J) rfl
  have step_same : ∀ (xs : List Event) (e : Event) (hc : ∀ q, (replay I xs).cs q = (replay J xs).cs q) (p : Proc),
      (replay I (xs ++ [e])).cs p = (replay J (xs ++ [e])).cs p := by
    intro xs e hc p
    rw [replay_append, replay_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hos := os_same xs
    cases e with
    | spawn pid =>
      cases hi : (replay I xs).os.table pid <;>
        cases hj : (replay J xs).os.table pid <;>
        simp [step, hi, hj, hc p]
    | exit pid =>
      cases hi : (replay I xs).os.table pid with
      | none =>
        have hj : (replay J xs).os.table pid = none := by rw [← hos]; exact hi
        simp [step, hi, hj]
        exact hc p
      | some tok =>
        have hj : (replay J xs).os.table pid = some tok := by rw [← hos]; exact hi
        simp only [step, hi, hj, setCS]
        by_cases hp : p = ⟨pid, tok⟩
        · simp [hp]
        · simp [hp, hc p]
    | acquire pid =>
      cases hi : (replay I xs).os.table pid with
      | none =>
        have hj : (replay J xs).os.table pid = none := by rw [← hos]; exact hi
        simp [step, hi, hj]
        exact hc p
      | some tok =>
        have hj : (replay J xs).os.table pid = some tok := by rw [← hos]; exact hi
        simp only [step, hi, hj]
        by_cases hp : p = ⟨pid, tok⟩
        · cases hgI : grants I (replay I xs) <;>
            cases hgJ : grants J (replay J xs) <;>
            simp [setCS, hp, hgI, hgJ]
        · have hold : (replay I xs).cs p = false := by
            by_cases htrue : (replay I xs).cs p = true
            · by_cases hex : ∃ q, (replay I xs).cs q = true
              · obtain ⟨q, hq⟩ := hex
                by_cases hqt : q = ⟨pid, tok⟩
                · rw [hqt] at hq
                  exact False.elim (hp (by rw [← hqt]; exact congrArg id (hc q).symm))
                · have hgr : grants I (replay I xs) = false := by
                    by_contra hn
                    have hgt : grants I (replay I xs) = true := Bool.eq_true_of_not_eq_false hn
                    have ht : (replay I (xs ++ [.acquire pid])).cs ⟨pid, tok⟩ = true := by
                      simp [replay_append, step, hi, hgt, setCS]
                    have hq' : (replay I (xs ++ [.acquire pid])).cs q = true := by
                      simp [replay_append, step, hi, hqt, hq]
                    exact hqt (hI.1 _ _ ht hq')
                  exact False.elim (by
                    have := hI.1 _ _ htrue htrue
                    exact this rfl)
              · exact False.elim (htrue (by simp [hex]))
            · exact Bool.eq_false_of_not_eq_true htrue
          have hgrI : grants I (replay I xs) = false := by
            by_cases hex : ∃ q, (replay I xs).cs q = true
            · obtain ⟨q, hq⟩ := hex
              by_cases hqt : q = ⟨pid, tok⟩
              · exfalso
                apply hp
                rw [← hqt]
                exact congrArg id (hc q).symm
              · by_contra hn
                have hgt : grants I (replay I xs) = true := Bool.eq_true_of_not_eq_false hn
                have ht : (replay I (xs ++ [.acquire pid])).cs ⟨pid, tok⟩ = true := by
                  simp [replay_append, step, hi, hgt, setCS]
                have hq' : (replay I (xs ++ [.acquire pid])).cs q = true := by
                  simp [replay_append, step, hi, hqt, hq]
                exact hqt (hI.1 _ _ ht hq')
            · exfalso
              have hf : grants I (replay I xs) = false := by assumption
              obtain ⟨q, hq, _⟩ := hI.2.1 xs hf
              exact hex ⟨q, hq⟩
          have hgrJ : grants J (replay J xs) = false := by
            by_contra hn
            have hgt : grants J (replay J xs) = true := Bool.eq_true_of_not_eq_false hn
            have hqJ : (replay J xs).cs p = false := by simpa [hc p] using hhold
            by_cases hex : ∃ q, (replay J xs).cs q = true
            · obtain ⟨q, hq⟩ := hex
              by_cases hqt : q = ⟨pid, tok⟩
              · exact hp (by rw [← hqt]; exact congrArg id (hc q).symm)
              · have ht : (replay J (xs ++ [.acquire pid])).cs ⟨pid, tok⟩ = true := by simp [replay_append, step, hi, hgt, setCS]
                have hq' : (replay J (xs ++ [.acquire pid])).cs q = true := by simp [replay_append, step, hj, hqt, hq]
                exact hqt (hJ.1 _ _ ht hq')
            · have := hJ.2.1 xs (by exact Bool.eq_false_of_not_eq_true (by intro h; exact hex (by simpa [h] using h)))
              exact hex ⟨this.choose, this.choose_spec.1⟩
          simp [setCS, hp, hgrI, hgrJ, hhold, hc p]
    | release pid =>
      by_cases hp : (replay I xs).cs p = true
      · by_cases hpid : p.pid = pid
        · have hi' := hI.2.2.2 xs p hp
          have hj' := hJ.2.2.2 xs p (by rw [← hc p]; exact hp)
          simpa [replay_append, step] using congrArg id (Eq.trans hi'.symm hj')
        · have hi' := hI.2.2.1 xs (.release pid) p hp (by simp [hpid]) (by simp [hpid])
          have hj' := hJ.2.2.1 xs (.release pid) p (by rw [← hc p]; exact hp) (by simp [hpid]) (by simp [hpid])
          simpa [replay_append, step] using congrArg id (Eq.trans hi'.2.symm hj'.2)
      · simp only [step]
        cases hi : (replay I xs).os.table pid <;> simp [hi, setCS, hp, hc p]
  have aux : ∀ (pre rest : List Event),
      (replay I pre).os = (replay J pre).os →
      (∀ q, (replay I pre).cs q = (replay J pre).cs q) →
      (rest.foldl (step I) (replay I pre)).os = (rest.foldl (step J) (replay J pre)).os ∧
      (∀ q, (rest.foldl (step I) (replay I pre)).cs q = (rest.foldl (step J) (replay J pre)).cs q) := by
    intro pre rest
    induction rest with
    | nil => intro ho hc; exact ⟨ho, hc⟩
    | cons e es ih =>
      intro ho hc
      simp only [List.foldl_cons]
      have hcs : ∀ q, (step I (replay I pre) e).cs q = (step J (replay J pre) e).cs q := by
        intro q
        exact step_same pre e hc q
      have hos : (step I (replay I pre) e).os = (step J (replay J pre) e).os := step_os _ _ e ho
      exact ih (pre := pre ++ [e]) (by simpa [replay_append] using hos) (by simpa [replay_append] using hcs)
  intro evs p
  exact (aux [] evs rfl (by intro q; rfl)).2 p

end Complete
