import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

def designA : SyncImpl := refSync

def designB : SyncImpl :=
  fun c st r => r ++ ((st.filter (absent r)).map (adjust c) ++ (st.filter (absent r)).map (adjust c))

def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 1, 1, true⟩]
def registry : List Entry := []

theorem a_passes : Passes designA :=
  ⟨Sync.ref_keeps_rows, Sync.ref_only_absent_starter, Sync.ref_nothing_left,
   Sync.ref_disabled_by_default, Sync.ref_locked_stays_disabled,
   Sync.ref_enable_keeps_starter_state, Sync.ref_idempotent⟩

private theorem b_eq (c : Config) (st r added : List Entry)
    (h : designB c st r = r ++ added) :
    added = (st.filter (absent r)).map (adjust c) ++ (st.filter (absent r)).map (adjust c) :=
  (List.append_cancel_left h).symm

private theorem b_mem (c : Config) (st r added : List Entry) (h : designB c st r = r ++ added)
    (a : Entry) (ha : a ∈ added) : ∃ s ∈ st, absent r s = true ∧ a = adjust c s := by
  have := b_eq c st r added h
  subst this
  rcases List.mem_append.mp ha with ha | ha <;>
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
    exact ⟨s, (List.mem_filter.mp hs).1, (List.mem_filter.mp hs).2, rfl⟩

private theorem b_nothing : NothingLeft designB := by
  intro c st r s hs ha
  have h := Sync.ref_nothing_left c st r s hs ha
  simp only [refSync, hasId, List.any_append] at h ⊢
  simp only [designB, List.any_append]
  simp_all

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, b_nothing, ?_, ?_, ?_, ?_⟩
  · intro c st r; exact ⟨_, rfl⟩
  · intro c st r added h a ha
    obtain ⟨s, hs, hab, rfl⟩ := b_mem c st r added h a ha
    exact ⟨s, hs, hab, Sync.adjust_id c s, Sync.adjust_adapter c s, Sync.adjust_model c s⟩
  · intro c st r added hen h a ha
    obtain ⟨s, _, _, rfl⟩ := b_mem c st r added h a ha
    exact Sync.adjust_enabled_false c s hen
  · intro c st r added h a ha hl
    obtain ⟨s, _, _, rfl⟩ := b_mem c st r added h a ha
    rw [Sync.adjust_adapter] at hl
    unfold adjust
    split <;> simp_all
  · intro c st r added _ hen h a ha hl
    obtain ⟨s, hs, _, rfl⟩ := b_mem c st r added h a ha
    rw [Sync.adjust_adapter] at hl
    refine ⟨s, hs, (Sync.adjust_id c s).symm, ?_⟩
    unfold adjust
    simp [hen, hl]
  · intro c st r
    have : st.filter (absent (designB c st r)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s hs hab
      have h1 : absent r s = true := by
        have : designB c st r = r ++ _ := rfl
        rw [this] at hab
        exact Sync.absent_append _ _ _ hab
      have h3 : hasId (designB c st r) s.id = true := b_nothing c st r s hs h1
      simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
      rw [hab.1] at h3
      exact absurd h3 (by simp)
    show designB c st (designB c st r) = designB c st r
    show designB c st r ++ (_ ++ _) = designB c st r
    rw [this]; simp

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  rw [hs, hs']

theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
