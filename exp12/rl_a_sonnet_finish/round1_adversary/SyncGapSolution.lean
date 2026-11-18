import Sync
import SyncLaws

open Sync

namespace SyncGap

def dedup : List Entry → List Entry
  | [] => []
  | a :: t => if a ∈ t then dedup t else a :: dedup t

theorem dedup_sub : ∀ l : List Entry, List.Sublist (dedup l) l
  | [] => by simp [dedup]
  | a :: t => by
    unfold dedup
    split
    · exact (dedup_sub t).cons _
    · exact (dedup_sub t).cons_cons _

theorem dedup_mem : ∀ l : List Entry, ∀ x ∈ l, x ∈ dedup l
  | [], x, h => by simp at h
  | a :: t, x, h => by
    unfold dedup
    split
    · rename_i hat
      rcases List.mem_cons.mp h with rfl | h
      · exact dedup_mem t _ hat
      · exact dedup_mem t _ h
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (dedup_mem t _ h)

theorem gen (S : List Entry → List Entry → List Entry)
    (hsub : ∀ st r, List.Sublist (S st r) (st.filter (absent r)))
    (hmem : ∀ st r, ∀ s ∈ st.filter (absent r), s ∈ S st r) :
    Passes (fun c st r => r ++ (S st r).map (adjust c)) := by
  have adj_id : ∀ c s, (adjust c s).id = s.id := by
    intro c s; simp [adjust]; split <;> simp
  have key : ∀ st r s, s ∈ S st r → s ∈ st ∧ absent r s = true := by
    intro st r s h
    exact List.mem_filter.mp ((hsub st r).subset h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r _ x hx hxr
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with h | ⟨s, hs, rfl⟩
    · exact absurd h hxr
    · obtain ⟨hs1, ha⟩ := key _ _ _ hs
      exact ⟨s, hs1, ha, by simp [adjust]; split <;> simp, by simp [adjust]; split <;> simp,
        by simp [adjust]; split <;> simp⟩
  · intro c st r _ s hs ha
    refine ⟨adjust c s, ?_, ?_⟩
    · simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨s, hmem st r s (List.mem_filter.mpr ⟨hs, ha⟩), rfl⟩
    · simp [adjust]; split <;> simp
  · intro c st r _ x hx hxr
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with h | ⟨s, hs, rfl⟩
    · exact absurd h hxr
    · obtain ⟨hs1, ha⟩ := key _ _ _ hs
      have : (adjust c s).adapter = s.adapter := by simp [adjust]; split <;> simp
      have h2 : (adjust c s).model = s.model := by simp [adjust]; split <;> simp
      rw [this, h2]
      simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      simpa using ha.2
  · intro c st r hd he s hs ha x hx hid
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with h | ⟨s', hs', rfl⟩
    · simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      have : hasId r s.id = true := by
        simp only [hasId, List.any_eq_true, beq_iff_eq]
        exact ⟨x, h, hid⟩
      simp [ha.1] at this
    · simp only [adjust, he]; split <;> simp_all
  · intro c st r hd he s hs ha hl x hx hid
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with h | ⟨s', hs', rfl⟩
    · simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      have : hasId r s.id = true := by
        simp only [hasId, List.any_eq_true, beq_iff_eq]
        exact ⟨x, h, hid⟩
      simp [ha.1] at this
    · obtain ⟨hs1, _⟩ := key _ _ _ hs'
      have : s' = s := hd s' hs1 s hs (by rw [← adj_id c s']; exact hid)
      subst this
      simp only [adjust, he, hl]; split <;> simp_all
  · intro c st r hd s hs ha hl x hx hid
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with h | ⟨s', hs', rfl⟩
    · simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      have : hasId r s.id = true := by
        simp only [hasId, List.any_eq_true, beq_iff_eq]
        exact ⟨x, h, hid⟩
      simp [ha.1] at this
    · obtain ⟨hs1, _⟩ := key _ _ _ hs'
      have : s' = s := hd s' hs1 s hs (by rw [← adj_id c s']; exact hid)
      subst this
      simp only [adjust]; split <;> simp_all
  · intro c st r _
    refine ⟨_, rfl, ?_⟩
    rw [List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext (adj_id c)
    rw [this]
    exact ((hsub st r).trans List.filter_sublist).map _
  · intro c st r _ new hnew x hx
    have h1 : new = (S st r).map (adjust c) :=
      (List.append_cancel_left (as := r) hnew.symm)
    subst h1
    simp only [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨_, ha⟩ := key _ _ _ hs
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
    rw [adj_id]; exact ha.1

def designA : SyncImpl := fun c st r => r ++ ((st.filter (absent r))).map (adjust c)
def designB : SyncImpl := fun c st r => r ++ (dedup (st.filter (absent r))).map (adjust c)

def config : Config := ⟨fun _ => false, false⟩
def e0 : Entry := ⟨1, 1, 1, false⟩
def starter : List Entry := [e0, e0]
def registry : List Entry := []

theorem a_passes : Passes designA :=
  gen (fun st r => st.filter (absent r)) (fun _ _ => List.Sublist.refl _) (fun _ _ _ h => h)

theorem b_passes : Passes designB :=
  gen (fun st r => dedup (st.filter (absent r))) (fun _ _ => dedup_sub _) (fun _ _ => dedup_mem _)

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  subst hs; subst hs'; rfl

theorem differ : designA config starter registry ≠ designB config starter registry := by
  simp [designA, designB, starter, registry, e0, absent, hasId, hasIdentity, dedup, adjust, config]

end SyncGap
