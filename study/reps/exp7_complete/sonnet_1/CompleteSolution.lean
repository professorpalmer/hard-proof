import Laws

open Laws

namespace Complete

open Classical in
/-- Design-independent next critical-section set. -/
noncomputable def spec (os : OS) (c : Proc → Bool) : Event → Proc → Bool
  | .spawn _, p => c p
  | .exit pid, p =>
    match os.table pid with
    | none => c p
    | some t => if p = ⟨pid, t⟩ then false else c p
  | .acquire pid, p =>
    match os.table pid with
    | none => c p
    | some t =>
      if p = ⟨pid, t⟩ ∧ ∀ r, c r = true → ¬ os.live r then true else c p
  | .release pid, p =>
    match os.table pid with
    | none => c p
    | some t => if p = ⟨pid, t⟩ then false else c p

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

theorem step_os (I : LockImpl) (s : State I) (e : Event) :
    (step I s e).os = osStep s.os e := by
  cases e <;> simp only [step, osStep] <;> (repeat' split) <;> simp_all

theorem rev_ind (P : List Event → Prop) (h0 : P []) (hs : ∀ l e, P l → P (l ++ [e])) :
    ∀ l, P l := by
  intro l
  have key : ∀ m : List Event, P m.reverse := by
    intro m
    induction m with
    | nil => exact h0
    | cons a m ih => simpa using hs _ a ih
  simpa using key l.reverse

theorem os_eq (I J : LockImpl) (evs : List Event) :
    (replay I evs).os = (replay J evs).os := by
  induction evs using rev_ind with
  | h0 => rfl
  | hs evs e ih => rw [replay_snoc, replay_snoc, step_os, step_os, ih]

theorem cs_spec (I : LockImpl) (hI : Passes I) (evs : List Event) (e : Event) :
    (replay I (evs ++ [e])).cs = spec (replay I evs).os (replay I evs).cs e := by
  obtain ⟨hMutex, hNoOrphan, _hKeeps, hRel, _, _⟩ := hI
  funext p
  rw [replay_snoc]
  cases e with
  | spawn pid =>
    simp only [step, spec]
    split <;> rfl
  | exit pid =>
    simp only [step, spec]
    split <;> simp_all [setCS]
  | acquire pid =>
    cases ht : (replay I evs).os.table pid with
    | none => simp [step, spec, ht]
    | some t =>
      have hF1 := hNoOrphan evs
      have hF2 : ∀ r, (replay I evs).cs r = true → grants I (replay I evs) = true →
          r = ⟨pid, t⟩ := by
        intro r hr hg
        have h := hMutex (evs ++ [.acquire pid]) r ⟨pid, t⟩
        rw [replay_snoc] at h
        by_cases hne : r = ⟨pid, t⟩
        · exact hne
        · exfalso
          apply hne
          apply h
          · simp [step, ht, hg, setCS, hne, hr]
          · simp [step, ht, hg, setCS]
      by_cases hg : grants I (replay I evs) = true
      · by_cases hp : p = ⟨pid, t⟩
        · subst hp
          by_cases hall : ∀ r, (replay I evs).cs r = true → ¬ (replay I evs).os.live r
          · simp [step, spec, ht, hg, setCS]
            exact Or.inl hall
          · have hx : ∃ r, (replay I evs).cs r = true ∧ (replay I evs).os.live r := by
              by_cases hx : ∃ r, (replay I evs).cs r = true ∧ (replay I evs).os.live r
              · exact hx
              · exfalso; apply hall; intro r hr hl; exact hx ⟨r, hr, hl⟩
            obtain ⟨r, hr, _⟩ := hx
            have hq := hF2 r hr hg
            subst hq
            simp [step, spec, ht, hg, setCS, hall, hr]
        · simp [step, spec, ht, hg, setCS, hp]
      · have hg' : grants I (replay I evs) = false := by simpa using hg
        obtain ⟨r, hr, hl⟩ := hF1 hg'
        have hall : ¬ ∀ r, (replay I evs).cs r = true → ¬ (replay I evs).os.live r :=
          fun h => h r hr hl
        simp [step, spec, ht, hg', hall]
  | release pid =>
    cases ht : (replay I evs).os.table pid with
    | none => simp [step, spec, ht]
    | some t =>
      by_cases hp : p = ⟨pid, t⟩
      · subst hp
        by_cases hc : (replay I evs).cs ⟨pid, t⟩ = true
        · have h := hRel evs ⟨pid, t⟩ hc
          rw [replay_snoc] at h
          simp [spec, ht]
          simpa [step, ht] using h
        · have hc' : (replay I evs).cs ⟨pid, t⟩ = false := by simpa using hc
          simp only [step, spec, ht]
          split <;> split <;> simp [setCS, hc']
      · simp only [step, spec, ht]
        (repeat' split) <;> simp_all [setCS]

theorem cs_eq (I J : LockImpl) (hI : Passes I) (hJ : Passes J) (evs : List Event) :
    (replay I evs).cs = (replay J evs).cs := by
  induction evs using rev_ind with
  | h0 => rfl
  | hs evs e ih => rw [cs_spec I hI, cs_spec J hJ, ih, os_eq I J]

/-- The laws are complete. -/
theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs p
  rw [cs_eq I J hI hJ evs]

end Complete
