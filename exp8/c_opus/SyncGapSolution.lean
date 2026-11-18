import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The added rows of `refSync`. -/
def addedRows (c : Config) (st r : List Entry) : List Entry :=
  (st.filter (absent r)).map (adjust c)

/-- The first design: the model of the shipped code. -/
def designA : SyncImpl := refSync

/-- The second design: it appends each new row two times. -/
def designB : SyncImpl := fun c st r => r ++ (addedRows c st r ++ addedRows c st r)

def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 0, 0, false⟩]
def registry : List Entry := []

theorem refSync_eq (c : Config) (st r : List Entry) : refSync c st r = r ++ addedRows c st r := rfl

theorem b_added {c : Config} {st r added : List Entry} (h : designB c st r = r ++ added) :
    added = addedRows c st r ++ addedRows c st r :=
  (List.append_cancel_left (show r ++ (addedRows c st r ++ addedRows c st r) = r ++ added from h)).symm

theorem mem_dup {a : Entry} {l : List Entry} (h : a ∈ l ++ l) : a ∈ l := by
  rcases List.mem_append.mp h with h | h <;> exact h

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
   Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
   Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r; exact ⟨_, rfl⟩
  · intro c st r added h a ha
    rw [b_added h] at ha
    exact Sync.ref_only_absent_starter c st r _ (refSync_eq c st r) a (mem_dup ha)
  · intro c st r s hs hab
    have h := Sync.ref_nothing_left c st r s hs hab
    rw [refSync_eq] at h
    simp only [designB, hasId, List.any_append, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro c st r added hen h a ha
    rw [b_added h] at ha
    exact Sync.ref_disabled_by_default c st r _ hen (refSync_eq c st r) a (mem_dup ha)
  · intro c st r added h a ha hl
    rw [b_added h] at ha
    exact Sync.ref_locked_stays_disabled c st r _ (refSync_eq c st r) a (mem_dup ha) hl
  · intro c st r added hd hen h a ha hl
    rw [b_added h] at ha
    exact Sync.ref_enable_keeps_starter_state c st r _ hd hen (refSync_eq c st r) a (mem_dup ha) hl
  · intro c st r
    have hnil : st.filter (absent (designB c st r)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s hs hab
      have hab' : absent (refSync c st r) s = true := by
        rw [refSync_eq]
        have : designB c st r = (r ++ addedRows c st r) ++ addedRows c st r := by
          simp [designB]
        rw [this] at hab
        exact Sync.absent_append _ _ _ hab
      have h1 := Sync.absent_append _ _ _ hab'
      have h2 := Sync.ref_nothing_left c st r s hs h1
      simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab'
      rw [hab'.1] at h2
      exact absurd h2 (by simp)
    show designB c st r ++ (addedRows c st (designB c st r) ++ addedRows c st (designB c st r))
      = designB c st r
    simp only [addedRows] at hnil ⊢
    rw [hnil]; simp

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  rw [hs, hs']

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
