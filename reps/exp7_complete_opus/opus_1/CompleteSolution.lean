import Laws

open Laws

namespace Complete

open Classical in
/-- The critical-section update that each passing design must follow. -/
noncomputable def csStep (os : OS) (cs : Proc → Bool) : Event → Proc → Bool
  | .spawn _ => cs
  | .exit pid =>
    match os.table pid with
    | none => cs
    | some t => setCS cs ⟨pid, t⟩ false
  | .acquire pid =>
    match os.table pid with
    | none => cs
    | some t =>
      if ∃ q, cs q = true ∧ q ≠ ⟨pid, t⟩ then cs else setCS cs ⟨pid, t⟩ true
  | .release pid =>
    match os.table pid with
    | none => cs
    | some t => setCS cs ⟨pid, t⟩ false

/-- The OS update. It does not depend on the design. -/
def osStep (os : OS) : Event → OS
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

theorem replay_snoc (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

theorem os_step (I : LockImpl) (s : State I) (e : Event) :
    (step I s e).os = osStep s.os e := by
  cases e with
  | spawn pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | exit pid => cases h : s.os.table pid <;> simp [step, osStep, h]
  | acquire pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some t => simp only [step, osStep, h]; split <;> rfl
  | release pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some t =>
      simp only [step, osStep, h]
      cases s.owner with
      | none => rfl
      | some r => simp only; split <;> rfl

theorem cs_step (I : LockImpl) (hI : Passes I) (evs : List Event) (e : Event) :
    (step I (replay I evs) e).cs = csStep (replay I evs).os (replay I evs).cs e := by
  obtain ⟨hMutex, hNoOrphan, _, hRel, _, _⟩ := hI
  cases e with
  | spawn pid =>
    cases h : (replay I evs).os.table pid <;> simp [step, csStep, h]
  | exit pid =>
    cases h : (replay I evs).os.table pid <;> simp [step, csStep, h]
  | acquire pid =>
    have hsn := replay_snoc I evs (.acquire pid)
    cases h : (replay I evs).os.table pid with
    | none => simp [step, csStep, h]
    | some t =>
      simp only [step, csStep, h]
      cases hg : grants I (replay I evs) with
      | true =>
        simp only [ite_true]
        by_cases hex : ∃ q, (replay I evs).cs q = true ∧ q ≠ ⟨pid, t⟩
        · exfalso
          obtain ⟨q, hq, hne⟩ := hex
          have hm := hMutex (evs ++ [.acquire pid]) q ⟨pid, t⟩
          rw [hsn] at hm
          simp only [step, h, hg, ite_true, setCS] at hm
          exact hne (hm (by simp [hne, hq]) (by simp))
        · simp [hex]
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        by_cases hex : ∃ q, (replay I evs).cs q = true ∧ q ≠ ⟨pid, t⟩
        · simp [hex]
        · simp only [hex, ite_false]
          obtain ⟨q, hq, _⟩ := hNoOrphan evs hg
          have hqa : q = ⟨pid, t⟩ := by
            apply Classical.byContradiction
            intro hne; exact hex ⟨q, hq, hne⟩
          subst hqa
          funext x
          simp only [setCS]
          split
          · rename_i hx; subst hx; exact hq
          · rfl
  | release pid =>
    have hsn := replay_snoc I evs (.release pid)
    cases h : (replay I evs).os.table pid with
    | none => simp [step, csStep, h]
    | some t =>
      have hrf := hRel evs ⟨pid, t⟩
      rw [hsn] at hrf
      simp only [csStep, h]
      funext x
      by_cases hx : x = ⟨pid, t⟩
      · subst hx
        simp only [setCS, ite_true]
        cases hca : (replay I evs).cs ⟨pid, t⟩ with
        | true => exact hrf hca
        | false =>
          simp only [step, h]
          cases (replay I evs).owner with
          | none => exact hca
          | some r =>
            simp only
            split
            · simp [setCS]
            · exact hca
      · simp only [setCS, hx, ite_false, step, h]
        cases (replay I evs).owner with
        | none => rfl
        | some r =>
          simp only
          split
          · simp [setCS, hx]
          · rfl

theorem snoc_induction {P : List Event → Prop} (h0 : P [])
    (hs : ∀ evs e, P evs → P (evs ++ [e])) : ∀ evs, P evs := by
  intro evs
  rw [← List.reverse_reverse evs]
  induction evs.reverse with
  | nil => exact h0
  | cons e es ih => rw [List.reverse_cons]; exact hs _ e ih

theorem agree (I J : LockImpl) (hI : Passes I) (hJ : Passes J) (evs : List Event) :
    (replay I evs).os = (replay J evs).os ∧ (replay I evs).cs = (replay J evs).cs := by
  refine snoc_induction (P := fun evs =>
    (replay I evs).os = (replay J evs).os ∧ (replay I evs).cs = (replay J evs).cs)
    ⟨rfl, rfl⟩ ?_ evs
  intro evs e ih
  · obtain ⟨ho, hc⟩ := ih
    rw [replay_snoc, replay_snoc]
    refine ⟨?_, ?_⟩
    · rw [os_step, os_step, ho]
    · rw [cs_step I hI, cs_step J hJ, ho, hc]

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  rw [(agree I J hI hJ evs).2]

end Complete
