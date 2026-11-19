import Laws

open Laws

namespace Complete

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ
  have os_same : ∀ xs : List Event, (replay I xs).os = (replay J xs).os := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => rfl
    | @snoc xs e ih =>
      simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases e <;> simp [step, ih]
  have step_same : ∀ (xs : List Event) (e : Event) (p : Proc),
      (∀ q, (replay I xs).cs q = (replay J xs).cs q) →
      (replay I xs).os = (replay J xs).os →
      (replay I (xs ++ [e])).cs p = (replay J (xs ++ [e])).cs p := by
    intro xs e p hcs hos
    simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    cases e with
    | spawn pid =>
      cases htI : (replay I xs).os.table pid <;>
        cases htJ : (replay J xs).os.table pid <;>
        simp [step, htI, htJ, hos, hcs]
    | exit pid =>
      cases htI : (replay I xs).os.table pid <;>
        cases htJ : (replay J xs).os.table pid <;>
        simp [step, htI, htJ, hos, hcs]
    | acquire pid =>
      cases htI : (replay I xs).os.table pid with
      | none =>
        have htJ : (replay J xs).os.table pid = none := by simpa [hos] using htI
        simp [step, htI, htJ]
      | some t =>
        have htJ : (replay J xs).os.table pid = some t := by simpa [hos] using htI
        by_cases hex : ∃ q, (replay I xs).cs q = true
        · obtain ⟨q, hq⟩ := hex
          have hqJ : (replay J xs).cs q = true := by simpa [hcs q] using hq
          have noI : grants I (replay I xs) = false := by
            by_contra hn
            have hi : grants I (replay I xs) = true := by
              cases h : grants I (replay I xs) <;> simp_all
            have hnew : (replay I (xs ++ [.acquire pid])).cs ⟨pid, t⟩ = true := by
              simp [step, htI, hi]
            have hold : (replay I (xs ++ [.acquire pid])).cs q = true := by
              exact (hI.2.2.1 xs (.acquire pid) q hq (by decide) (by decide)).2
            have neq := hI.1 (xs ++ [.acquire pid]) q ⟨pid, t⟩ hold hnew
            exact Proc.noConfusion neq
          have noJ : grants J (replay J xs) = false := by
            by_contra hn
            have hj : grants J (replay J xs) = true := by
              cases h : grants J (replay J xs) <;> simp_all
            have hnew : (replay J (xs ++ [.acquire pid])).cs ⟨pid, t⟩ = true := by
              simp [step, htJ, hj]
            have hold : (replay J (xs ++ [.acquire pid])).cs q = true := by
              exact (hJ.2.2.1 xs (.acquire pid) q hqJ (by decide) (by decide)).2
            have neq := hJ.1 (xs ++ [.acquire pid]) q ⟨pid, t⟩ hold hnew
            exact Proc.noConfusion neq
          simp [step, htI, htJ, noI, noJ, hcs]
        · have yesI : grants I (replay I xs) = true := by
            cases h : grants I (replay I xs) with
            | false =>
              obtain ⟨q, hq, _⟩ := hI.2.1 xs h
              exact False.elim (hex ⟨q, hq⟩)
            | true => rfl
          have yesJ : grants J (replay J xs) = true := by
            cases h : grants J (replay J xs) with
            | false =>
              obtain ⟨q, hq, _⟩ := hJ.2.1 xs h
              exact False.elim (hex ⟨q, by simpa [hcs q] using hq⟩)
            | true => rfl
          simp [step, htI, htJ, yesI, yesJ, hex, hcs]
    | release pid =>
      cases htI : (replay I xs).os.table pid with
      | none =>
        have htJ : (replay J xs).os.table pid = none := by simpa [hos] using htI
        simp [step, htI, htJ]
      | some t =>
        have htJ : (replay J xs).os.table pid = some t := by simpa [hos] using htI
        by_cases hp : (replay I xs).cs ⟨pid, t⟩ = true
        · have hpJ : (replay J xs).cs ⟨pid, t⟩ = true := by simpa [hcs _] using hp
          have fi := hI.2.2.2.1 xs ⟨pid, t⟩ hp
          have fj := hJ.2.2.2.1 xs ⟨pid, t⟩ hpJ
          by_cases he : p = ⟨pid, t⟩ <;> simp [step, htI, htJ, he, fi, fj]
        · have hpJ : (replay J xs).cs ⟨pid, t⟩ ≠ true := by simpa [hcs _] using hp
          by_cases he : p = ⟨pid, t⟩ <;> simp [step, htI, htJ, he, hp, hpJ]
  intro evs
  induction evs using List.reverseRecOn with
  | nil => intro p; rfl
  | @snoc xs e ih =>
    intro p
    exact step_same xs e p ih (os_same xs)

end Complete
