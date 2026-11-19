import Laws

open Laws

namespace Complete

theorem replay_snoc (K : LockImpl) (evs : List Event) (e : Event) :
    replay K (evs ++ [e]) = step K (replay K evs) e := by
  simp [replay, List.foldl_append]

theorem step_os (K : LockImpl) (s : State K) (e : Event) :
    (step K s e).os = (match e with
      | .spawn pid => match s.os.table pid with
          | some _ => s.os
          | none => { table := setTable s.os.table pid (some s.os.next), next := s.os.next + 1 }
      | .exit pid => match s.os.table pid with
          | none => s.os
          | some _ => { s.os with table := setTable s.os.table pid none }
      | _ => s.os) := by
  cases e with
  | spawn pid => simp only [step]; cases s.os.table pid <;> rfl
  | exit pid => simp only [step]; cases s.os.table pid <;> rfl
  | acquire pid =>
    simp only [step]
    cases s.os.table pid with
    | none => rfl
    | some t => simp only []; split <;> rfl
  | release pid =>
    simp only [step]
    cases s.os.table pid with
    | none => rfl
    | some t =>
      simp only []
      cases s.owner with
      | none => rfl
      | some r => simp only []; split <;> rfl

theorem rel_cs (K : LockImpl) (hK : Passes K) (evs : List Event) (pid t : Nat)
    (ht : (replay K evs).os.table pid = some t) :
    (replay K (evs ++ [Event.release pid])).cs = setCS (replay K evs).cs ⟨pid, t⟩ false := by
  have hf := hK.2.2.2.1 evs ⟨pid, t⟩
  rw [replay_snoc] at hf ⊢
  simp only [step, ht] at hf ⊢
  cases hown : (replay K evs).owner with
  | none =>
    rw [hown] at hf
    simp only [] at hf ⊢
    funext q
    unfold setCS
    by_cases hq : q = ⟨pid, t⟩
    · subst hq
      simp
      by_cases hc : (replay K evs).cs ⟨pid, t⟩ = true
      · exact absurd (hf hc) (by simp [hc])
      · simpa using hc
    · simp [hq]
  | some r =>
    rw [hown] at hf
    simp only [] at hf ⊢
    split
    · rfl
    · funext q
      unfold setCS
      by_cases hq : q = ⟨pid, t⟩
      · subst hq
        simp
        by_cases hc : (replay K evs).cs ⟨pid, t⟩ = true
        · exact absurd (hf hc) (by simp_all)
        · simpa using hc
      · simp [hq]

open Classical in
theorem acq_cs (K : LockImpl) (hK : Passes K) (evs : List Event) (pid t : Nat)
    (ht : (replay K evs).os.table pid = some t) :
    (replay K (evs ++ [Event.acquire pid])).cs =
      (if ∃ h, (replay K evs).cs h = true then (replay K evs).cs
       else setCS (replay K evs).cs ⟨pid, t⟩ true) := by
  classical
  have hm := hK.1 (evs ++ [Event.acquire pid])
  have hn := hK.2.1 evs
  rw [replay_snoc] at hm ⊢
  simp only [step, ht] at hm ⊢
  by_cases hex : ∃ h, (replay K evs).cs h = true
  · rw [if_pos hex]
    obtain ⟨h, hh⟩ := hex
    by_cases hg : grants K (replay K evs) = true
    · simp only [hg, if_true] at hm ⊢
      have hph : (⟨pid, t⟩ : Proc) = h := by
        by_cases hq : (⟨pid, t⟩ : Proc) = h
        · exact hq
        · exact hm ⟨pid, t⟩ h (by simp [setCS]) (by simp [setCS, Ne.symm hq, hh]) 
      subst hph
      funext q
      unfold setCS
      by_cases hq : q = ⟨pid, t⟩
      · subst hq; simpa using hh.symm
      · simp [hq]
    · simp [hg]
  · rw [if_neg hex]
    have hg : grants K (replay K evs) = true := by
      cases hgv : grants K (replay K evs) with
      | true => rfl
      | false =>
        obtain ⟨q, hq, _⟩ := hn hgv
        exact absurd ⟨q, hq⟩ hex
    simp [hg]

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  classical
  intro I J hI hJ
  have key : ∀ r : List Event,
      (replay I r.reverse).os = (replay J r.reverse).os ∧
      (replay I r.reverse).cs = (replay J r.reverse).cs := by
    intro r
    induction r with
    | nil => exact ⟨rfl, rfl⟩
    | cons e r ih =>
      obtain ⟨ho, hc⟩ := ih
      rw [List.reverse_cons]
      generalize r.reverse = evs at ho hc ⊢
      have osI := step_os I (replay I evs) e
      have osJ := step_os J (replay J evs) e
      rw [← replay_snoc] at osI osJ
      refine ⟨?_, ?_⟩
      · rw [osI, osJ, ho]
      · cases e with
        | spawn pid =>
          rw [replay_snoc, replay_snoc]
          simp only [step]
          rw [ho]
          cases (replay J evs).os.table pid <;> simp [hc]
        | exit pid =>
          rw [replay_snoc, replay_snoc]
          simp only [step]
          rw [ho]
          cases (replay J evs).os.table pid <;> simp [hc]
        | release pid =>
          cases ht : (replay J evs).os.table pid with
          | none =>
            rw [replay_snoc, replay_snoc]
            simp only [step]
            rw [ho, ht]; exact hc
          | some t =>
            rw [rel_cs I hI evs pid t (by rw [ho]; exact ht), rel_cs J hJ evs pid t ht, hc]
        | acquire pid =>
          cases ht : (replay J evs).os.table pid with
          | none =>
            rw [replay_snoc, replay_snoc]
            simp only [step]
            rw [ho, ht]; exact hc
          | some t =>
            rw [acq_cs I hI evs pid t (by rw [ho]; exact ht), acq_cs J hJ evs pid t ht, hc]
  intro evs p
  have := (key evs.reverse).2
  rw [List.reverse_reverse] at this
  exact congrFun this p

end Complete
