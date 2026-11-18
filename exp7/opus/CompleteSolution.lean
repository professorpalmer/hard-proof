/-
Hard Proof, experiment 7. AGENT-OWNED FILE.

The laws are complete. The OS part of the state does not depend on the design.
In each reachable state, the laws fix the effect of each event on `cs`:
- acquire: when a process is in the critical section, `cs` does not change
  (Mutex, or the requester already holds). Else the lock must grant
  (NoOrphanHold), and the requester enters.
- release: the releaser leaves (ReleaseFrees), and no other process changes.
-/
import Laws

open Laws

namespace Complete

/-- The OS after one event. It does not depend on the design. -/
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

open Classical in
/-- The critical section after one event, as the laws fix it. -/
noncomputable def csStep (os : OS) (cs : Proc → Bool) : Event → Proc → Bool
  | .spawn _ => cs
  | .exit pid =>
    match os.table pid with
    | none => cs
    | some t => setCS cs ⟨pid, t⟩ false
  | .acquire pid =>
    match os.table pid with
    | none => cs
    | some t => if ∃ q, cs q = true then cs else setCS cs ⟨pid, t⟩ true
  | .release pid =>
    match os.table pid with
    | none => cs
    | some t => setCS cs ⟨pid, t⟩ false

theorem os_step (I : LockImpl) (s : State I) (e : Event) :
    (step I s e).os = osStep s.os e := by
  cases e with
  | spawn pid =>
    cases h : s.os.table pid <;> simp [step, osStep, h]
  | exit pid =>
    cases h : s.os.table pid <;> simp [step, osStep, h]
  | acquire pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some t =>
      simp only [step, osStep, h]
      split <;> rfl
  | release pid =>
    cases h : s.os.table pid with
    | none => simp [step, osStep, h]
    | some t =>
      simp only [step, osStep, h]
      split
      · rfl
      · split <;> rfl

theorem replay_snoc (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

theorem cs_step (I : LockImpl) (hI : Passes I) (evs : List Event) (e : Event) :
    (replay I (evs ++ [e])).cs = csStep (replay I evs).os (replay I evs).cs e := by
  obtain ⟨hMut, hNoOrph, _hKeep, hRel, _, _⟩ := hI
  rw [replay_snoc]
  cases e with
  | spawn pid =>
    cases h : (replay I evs).os.table pid <;> simp [step, csStep, h]
  | exit pid =>
    cases h : (replay I evs).os.table pid <;> simp [step, csStep, h]
  | acquire pid =>
    cases h : (replay I evs).os.table pid with
    | none => simp [step, csStep, h]
    | some t =>
      simp only [step, csStep, h]
      by_cases hex : ∃ q, (replay I evs).cs q = true
      · rw [if_pos hex]
        by_cases hg : grants I (replay I evs) = true
        · rw [if_pos hg]
          obtain ⟨q, hq⟩ := hex
          show setCS (replay I evs).cs ⟨pid, t⟩ true = (replay I evs).cs
          funext x
          unfold setCS
          split
          · next hx =>
            subst hx
            by_cases hqp : q = ⟨pid, t⟩
            · subst hqp; exact hq.symm
            · exfalso
              have hstep : replay I (evs ++ [Event.acquire pid]) =
                  { replay I evs with owner := some (I.record ⟨pid, t⟩),
                                      cs := setCS (replay I evs).cs ⟨pid, t⟩ true } := by
                rw [replay_snoc]; simp only [step, h, hg, ↓reduceIte]
              have h1 : (replay I (evs ++ [Event.acquire pid])).cs ⟨pid, t⟩ = true := by
                rw [hstep]; simp [setCS]
              have h2 : (replay I (evs ++ [Event.acquire pid])).cs q = true := by
                rw [hstep]; simp [setCS, hqp, hq]
              exact hqp (hMut _ _ _ h2 h1)
          · rfl
        · rw [if_neg hg]
      · rw [if_neg hex]
        have hg : grants I (replay I evs) = true := by
          cases hg' : grants I (replay I evs) with
          | true => rfl
          | false =>
            exfalso
            obtain ⟨q, hq, _⟩ := hNoOrph evs hg'
            exact hex ⟨q, hq⟩
        rw [if_pos hg]
  | release pid =>
    cases h : (replay I evs).os.table pid with
    | none => simp [step, csStep, h]
    | some t =>
      have hR : csStep (replay I evs).os (replay I evs).cs (.release pid) =
          setCS (replay I evs).cs ⟨pid, t⟩ false := by simp [csStep, h]
      rw [hR]
      have hfree : (replay I evs).cs ⟨pid, t⟩ = true →
          (replay I (evs ++ [Event.release pid])).cs ⟨pid, t⟩ = false :=
        fun hc => hRel evs ⟨pid, t⟩ hc
      rw [replay_snoc] at hfree
      have hkeep : ((replay I evs).cs ⟨pid, t⟩ = true → (replay I evs).cs ⟨pid, t⟩ = false) →
          (replay I evs).cs = setCS (replay I evs).cs ⟨pid, t⟩ false := by
        intro hk
        funext x
        by_cases hx : x = ⟨pid, t⟩
        · subst hx
          cases hc : (replay I evs).cs ⟨pid, t⟩ with
          | false => simp [setCS]
          | true => rw [hk hc] at hc; cases hc
        · simp [setCS, hx]
      simp only [step, h] at hfree ⊢
      cases ho : (replay I evs).owner with
      | none =>
        simp only [ho] at hfree ⊢
        exact hkeep hfree
      | some r =>
        simp only [ho] at hfree ⊢
        by_cases hown : I.isOwner r ⟨pid, t⟩ = true
        · simp only [hown, ↓reduceIte]
        · simp only [hown, Bool.false_eq_true, ↓reduceIte] at hfree ⊢
          exact hkeep hfree

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs
  have key : ∀ l : List Event, (replay I l.reverse).os = (replay J l.reverse).os ∧
      (replay I l.reverse).cs = (replay J l.reverse).cs := by
    intro l
    induction l with
    | nil => exact ⟨rfl, rfl⟩
    | cons e l ih =>
      obtain ⟨hos, hcs⟩ := ih
      rw [List.reverse_cons]
      refine ⟨?_, ?_⟩
      · rw [replay_snoc, replay_snoc, os_step, os_step, hos]
      · rw [cs_step I hI, cs_step J hJ, hos, hcs]
  intro p
  have k := (key evs.reverse).2
  rw [List.reverse_reverse] at k
  rw [k]

end Complete
