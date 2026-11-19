import Sync
import SyncLaws

open Sync

namespace SyncGap

def dd : List Entry → List Entry
  | [] => []
  | x :: xs => x :: dd (xs.filter (fun y => decide (y ≠ x)))
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  exact Nat.lt_succ_of_le (by simpa using List.length_filter_le _ xs.attach)

theorem dd_sub_mem : ∀ (n : Nat) (l : List Entry), l.length ≤ n →
    (dd l).Sublist l ∧ ∀ x, x ∈ dd l ↔ x ∈ l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst this; simp [dd]
  | succ n ih =>
    intro l hl
    match l with
    | [] => simp [dd]
    | x :: xs =>
      have hf : (xs.filter (fun y => decide (y ≠ x))).length ≤ n :=
        Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ hl)
      obtain ⟨h1, h2⟩ := ih _ hf
      rw [dd]
      refine ⟨?_, ?_⟩
      · exact (h1.trans List.filter_sublist).cons_cons x
      · intro y
        simp only [List.mem_cons, h2, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h | ⟨h, _⟩)
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · by_cases hy : y = x
            · exact Or.inl hy
            · exact Or.inr ⟨h, hy⟩

theorem dd_sublist (l : List Entry) : (dd l).Sublist l := (dd_sub_mem _ l (Nat.le_refl _)).1
theorem mem_dd (l : List Entry) (x : Entry) : x ∈ dd l ↔ x ∈ l :=
  (dd_sub_mem _ l (Nat.le_refl _)).2 x

def designA : SyncImpl := ref

def designB : SyncImpl := fun c st r => ref c (dd st) r

def x : Entry := ⟨0, 0, 0, true⟩
def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [x, x]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  have hd : ∀ st, DistinctIds st → DistinctIds (dd st) := by
    intro st h s hs s' hs' e
    exact h s ((mem_dd _ _).mp hs) s' ((mem_dd _ _).mp hs') e
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := ref_passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r h; exact p1 c (dd st) r (hd st h)
  · intro c st r h; exact p2 c (dd st) r (hd st h)
  · intro c st r t h hf e he
    obtain ⟨s, hs, a, b⟩ := p3 c (dd st) r t (hd st h) hf e he
    exact ⟨s, (mem_dd _ _).mp hs, a, b⟩
  · intro c st r t h hf s hs ha
    exact p4 c (dd st) r t (hd st h) hf s ((mem_dd _ _).mpr hs) ha
  · intro c st r t h hc hf e he; exact p5 c (dd st) r t (hd st h) hc hf e he
  · intro c st r t h hf e he; exact p6 c (dd st) r t (hd st h) hf e he
  · intro c st r t h hc hf e he s hs
    exact p7 c (dd st) r t (hd st h) hc hf e he s ((mem_dd _ _).mpr hs)
  · intro c st r t h hf
    exact (p8 c (dd st) r t (hd st h) hf).trans ((dd_sublist st).map _)

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  rw [hs, hs']

theorem differ : designA config starter registry ≠ designB config starter registry := by
  intro h
  have := congrArg List.length h
  simp [designA, designB, ref, dd, starter, registry, config, x, absent, hasId, hasIdentity] at this

end SyncGap
