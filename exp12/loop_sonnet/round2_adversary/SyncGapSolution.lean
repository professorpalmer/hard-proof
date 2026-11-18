import Sync
import SyncLaws

open Sync

namespace SyncGap

def designA : SyncImpl := ref

def extra (st r : List Entry) : List Entry :=
  match st with
  | s :: _ => (r.filter (fun e => e.id == s.id)).take 1
  | [] => []

def designB : SyncImpl := fun c st r =>
  if st.any (absent r) = true then ref c st r else r ++ extra st r

def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [⟨1, 1, 1, true⟩]
def registry : List Entry := [⟨1, 1, 1, true⟩]

theorem a_passes : Passes designA := ref_passes

theorem extra_mem (st r : List Entry) : ∀ x ∈ extra st r, x ∈ r := by
  intro x hx
  unfold extra at hx
  split at hx
  · exact (List.mem_filter.mp (List.mem_of_mem_take hx)).1
  · simp at hx

theorem extra_sub (st r : List Entry) : List.Sublist ((extra st r).map Entry.id) (st.map Entry.id) := by
  unfold extra
  split
  · rename_i s t
    simp only [List.map_cons]
    have hall : ∀ y ∈ (((r.filter (fun e => e.id == s.id)).take 1).map Entry.id), y = s.id := by
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨e, he, rfl⟩ := hy
      have := (List.mem_filter.mp (List.mem_of_mem_take he)).2
      simpa using this
    have hlen : (((r.filter (fun e => e.id == s.id)).take 1).map Entry.id).length ≤ 1 := by
      simp; omega
    generalize (((r.filter (fun e => e.id == s.id)).take 1).map Entry.id) = l at hall hlen
    match l, hall, hlen with
    | [], _, _ => exact List.nil_sublist _
    | [y], h, _ =>
      have : y = s.id := h y (by simp)
      subst this
      exact List.Sublist.cons_cons _ (List.nil_sublist _)
    | _ :: _ :: _, _, h => simp at h
  · simp

theorem b_passes : Passes designB := by
  have hR := ref_passes
  obtain ⟨k, o, a, n, d, e, l, s⟩ := hR
  have key : ∀ (c : Config) (st r : List Entry), st.any (absent r) = true → designB c st r = ref c st r := by
    intro c st r h; simp [designB, h]
  have key2 : ∀ (c : Config) (st r : List Entry), ¬ st.any (absent r) = true → designB c st r = r ++ extra st r := by
    intro c st r h; simp [designB, h]
  have hasany : ∀ (st r : List Entry) (s : Entry), s ∈ st → absent r s = true → st.any (absent r) = true :=
    fun st r s hs ha => List.any_eq_true.mpr ⟨s, hs, ha⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r hd
    by_cases h : st.any (absent r) = true
    · rw [key c st r h]; exact k c st r hd
    · rw [key2 c st r h]; exact ⟨_, rfl⟩
  · intro c st r hd x hx hxr
    by_cases h : st.any (absent r) = true
    · rw [key c st r h] at hx; exact o c st r hd x hx hxr
    · rw [key2 c st r h] at hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact absurd hx hxr
      · exact absurd (extra_mem st r x hx) hxr
  · intro c st r hd s hs ha
    have h := hasany st r s hs ha
    rw [key c st r h]; exact a c st r hd s hs ha
  · intro c st r hd x hx hxr
    by_cases h : st.any (absent r) = true
    · rw [key c st r h] at hx; exact n c st r hd x hx hxr
    · rw [key2 c st r h] at hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact absurd hx hxr
      · exact absurd (extra_mem st r x hx) hxr
  · intro c st r hd he s hs ha x hx hid
    have h := hasany st r s hs ha
    rw [key c st r h] at hx; exact d c st r hd he s hs ha x hx hid
  · intro c st r hd he s hs ha hl x hx hid
    have h := hasany st r s hs ha
    rw [key c st r h] at hx; exact e c st r hd he s hs ha hl x hx hid
  · intro c st r hd s' hs ha hl x hx hid
    have h := hasany st r s' hs ha
    rw [key c st r h] at hx; exact l c st r hd s' hs ha hl x hx hid
  · intro c st r hd new hnew
    by_cases h : st.any (absent r) = true
    · rw [key c st r h] at hnew; exact s c st r hd new hnew
    · rw [key2 c st r h] at hnew
      have := List.append_cancel_left hnew
      subst this
      exact extra_sub st r

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'; subst hs; subst hs'; rfl

theorem differ : designA config starter registry ≠ designB config starter registry := by
  intro h
  have h2 : (ref config starter registry) = registry := by
    simp [ref, absent, hasId, hasIdentity, starter, registry]
  have h3 : designB config starter registry = registry ++ [⟨1,1,1,true⟩] := by
    simp [designB, absent, hasId, hasIdentity, starter, registry, extra]
  have : designA config starter registry = registry := h2
  rw [this, h3] at h
  simp [registry] at h

end SyncGap
