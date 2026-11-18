import Laws

open Laws

namespace Complete

theorem replay_snoc' (I : LockImpl) (evs : List Event) (e : Event) :
    replay I (evs ++ [e]) = step I (replay I evs) e := by
  simp [replay, List.foldl_append]

theorem acq_none (I : LockImpl) (hp : Passes I) (evs : List Event) (pid tok : Nat)
    (ht : (replay I evs).os.table pid = some tok)
    (hn : ∀ p, (replay I evs).cs p = false) :
    (replay I (evs ++ [Event.acquire pid])).cs = setCS (replay I evs).cs ⟨pid, tok⟩ true := by
  have hg : grants I (replay I evs) = true := by
    cases hg : grants I (replay I evs)
    · obtain ⟨q, hq, _⟩ := hp.2.1 evs hg
      rw [hn q] at hq; cases hq
    · rfl
  rw [replay_snoc']
  simp only [step, ht, hg, if_true]

theorem acq_some (I : LockImpl) (hp : Passes I) (evs : List Event) (pid tok : Nat)
    (ht : (replay I evs).os.table pid = some tok) (p : Proc)
    (hc : (replay I evs).cs p = true) :
    (replay I (evs ++ [Event.acquire pid])).cs = (replay I evs).cs := by
  by_cases hq : (⟨pid, tok⟩ : Proc) = p
  · rw [replay_snoc']
    by_cases hg : grants I (replay I evs) = true
    · simp only [step, ht, hg, if_true]
      funext r
      by_cases hr : r = ⟨pid, tok⟩
      · subst hr; simp [setCS, hq, hc]
      · simp [setCS, hr]
    · have hg' : grants I (replay I evs) = false := by simpa using hg
      simp only [step, ht, hg', Bool.false_eq_true, if_false]
  · have hg : grants I (replay I evs) = false := by
      cases h' : grants I (replay I evs)
      · rfl
      exfalso
      have h1 : (replay I (evs ++ [Event.acquire pid])).cs ⟨pid, tok⟩ = true := by
        rw [replay_snoc']; simp [step, ht, h', setCS]
      have h2 := (hp.2.2.1 evs (Event.acquire pid) p hc (by simp) (by simp)).2
      exact hq (hp.1 _ _ _ h1 h2)
    rw [replay_snoc']
    simp only [step, ht, hg, Bool.false_eq_true, if_false]

theorem rel_cs (I : LockImpl) (hp : Passes I) (evs : List Event) (pid tok : Nat)
    (ht : (replay I evs).os.table pid = some tok) :
    (replay I (evs ++ [Event.release pid])).cs = setCS (replay I evs).cs ⟨pid, tok⟩ false := by
  funext r
  by_cases hr : r = ⟨pid, tok⟩
  · subst hr
    by_cases hc : (replay I evs).cs ⟨pid, tok⟩ = true
    · have := hp.2.2.2.1 evs ⟨pid, tok⟩ hc
      simpa [setCS] using this
    · have hc' : (replay I evs).cs ⟨pid, tok⟩ = false := by simpa using hc
      rw [replay_snoc']
      simp only [step, ht]
      cases ho : (replay I evs).owner with
      | none => simpa [setCS] using hc'
      | some o =>
        by_cases hio : I.isOwner o ⟨pid, tok⟩ = true
        · simp [hio, setCS]
        · simp [hio, setCS, hc']
  · rw [replay_snoc']
    simp only [step, ht]
    cases ho : (replay I evs).owner with
    | none => simp [setCS, hr]
    | some o =>
      by_cases hio : I.isOwner o ⟨pid, tok⟩ = true
      · simp [hio, setCS, hr]
      · simp [hio, setCS, hr]

theorem laws_complete : ∀ (I J : LockImpl), Passes I → Passes J →
    ∀ (evs : List Event) (p : Proc), (replay I evs).cs p = (replay J evs).cs p := by
  intro I J hI hJ evs
  have key0 : ∀ l : List Event, (replay I l.reverse).os.table = (replay J l.reverse).os.table ∧
      (replay I l.reverse).os.next = (replay J l.reverse).os.next ∧
      (replay I l.reverse).cs = (replay J l.reverse).cs := by
    intro l
    induction l with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons e l ih =>
      rw [List.reverse_cons]
      generalize l.reverse = evs at ih ⊢
      obtain ⟨h1, h2, h3⟩ := ih
      cases e with
      | spawn pid =>
        rw [replay_snoc', replay_snoc']
        cases hp : (replay I evs).os.table pid with
        | some t0 =>
          have hp' : (replay J evs).os.table pid = some t0 := by rw [← h1]; exact hp
          simp only [step, hp, hp']; exact ⟨h1, h2, h3⟩
        | none =>
          have hp' : (replay J evs).os.table pid = none := by rw [← h1]; exact hp
          simp [step, hp, hp', h1, h2, h3]
      | exit pid =>
        rw [replay_snoc', replay_snoc']
        cases hp : (replay I evs).os.table pid with
        | none =>
          have hp' : (replay J evs).os.table pid = none := by rw [← h1]; exact hp
          simp only [step, hp, hp']; exact ⟨h1, h2, h3⟩
        | some t0 =>
          have hp' : (replay J evs).os.table pid = some t0 := by rw [← h1]; exact hp
          simp [step, hp, hp', h1, h2, h3]
      | acquire pid =>
        cases hp : (replay I evs).os.table pid with
        | none =>
          have hp' : (replay J evs).os.table pid = none := by rw [← h1]; exact hp
          rw [replay_snoc', replay_snoc']
          simp only [step, hp, hp']; exact ⟨h1, h2, h3⟩
        | some t0 =>
          have hp' : (replay J evs).os.table pid = some t0 := by rw [← h1]; exact hp
          have hos : ∀ (K : LockImpl), (replay K (evs ++ [Event.acquire pid])).os =
              (replay K evs).os := by
            intro K
            rw [replay_snoc']
            simp only [step]
            split
            · rfl
            · split <;> rfl
          refine ⟨?_, ?_, ?_⟩
          · rw [hos, hos]; exact h1
          · rw [hos, hos]; exact h2
          · by_cases hs : ∃ q, (replay I evs).cs q = true
            · obtain ⟨q, hq⟩ := hs
              rw [acq_some I hI evs pid t0 hp q hq,
                acq_some J hJ evs pid t0 hp' q (by rw [← h3]; exact hq)]
              exact h3
            · have hn : ∀ q, (replay I evs).cs q = false := by
                intro q; cases h : (replay I evs).cs q
                · rfl
                · exact absurd ⟨q, h⟩ hs
              rw [acq_none I hI evs pid t0 hp hn,
                acq_none J hJ evs pid t0 hp' (by intro q; rw [← h3]; exact hn q), h3]
      | release pid =>
        cases hp : (replay I evs).os.table pid with
        | none =>
          have hp' : (replay J evs).os.table pid = none := by rw [← h1]; exact hp
          rw [replay_snoc', replay_snoc']
          simp only [step, hp, hp']; exact ⟨h1, h2, h3⟩
        | some t0 =>
          have hp' : (replay J evs).os.table pid = some t0 := by rw [← h1]; exact hp
          have hos : ∀ (K : LockImpl), (replay K (evs ++ [Event.release pid])).os =
              (replay K evs).os := by
            intro K
            rw [replay_snoc']
            simp only [step]
            split
            · rfl
            · split
              · rfl
              · split <;> rfl
          refine ⟨?_, ?_, ?_⟩
          · rw [hos, hos]; exact h1
          · rw [hos, hos]; exact h2
          · rw [rel_cs I hI evs pid t0 hp, rel_cs J hJ evs pid t0 hp', h3]
  intro p
  have := (key0 evs.reverse).2.2
  rw [List.reverse_reverse] at this
  rw [this]

end Complete
