import Sync
import SyncLaws

open Sync

namespace SyncGap

def gen (g : List Entry → List Entry) : SyncImpl :=
  fun c st r => r ++ (g (st.filter (absent r))).map (adjust c)

theorem hid (c : Config) (s : Entry) :
    (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
  unfold adjust
  split <;> simp

theorem hen (c : Config) (s : Entry) :
    (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
  rcases c with ⟨lk, ce⟩
  rcases s with ⟨i, a, m, en⟩
  unfold adjust
  cases en <;> cases ce <;> cases hl : lk a <;> simp [hl]

theorem hdistinct : ∀ (st : List Entry) (s t : Entry), DistinctIds st →
    s ∈ st → t ∈ st → s.id = t.id → s = t := by
  intro st
  induction st with
  | nil => intro s t _ hs; simp at hs
  | cons a rest ih =>
    intro s t hd hs ht hst
    unfold DistinctIds at hd
    rw [List.pairwise_cons] at hd
    obtain ⟨hA, hR⟩ := hd
    rcases List.mem_cons.1 hs with rfl | hs'
    · rcases List.mem_cons.1 ht with rfl | ht'
      · rfl
      · exact absurd hst (hA t ht')
    · rcases List.mem_cons.1 ht with rfl | ht'
      · exact absurd hst.symm (hA s hs')
      · exact ih s t hR hs' ht' hst

theorem gen_passes (g : List Entry → List Entry) (hg : ∀ l e, e ∈ g l ↔ e ∈ l) :
    Passes (gen g) := by
  unfold Passes AppendsAbsent OnlyLacking NewEntryEnabled NotAddedByIdentity RowsKept
  have hback : ∀ (c : Config) (st r : List Entry) (s : Entry),
      s ∈ st → absent r s = true → adjust c s ∈ gen g c st r := by
    intro c st r s hs ha
    simp only [gen]
    exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨s, (hg _ _).2 (List.mem_filter.2 ⟨hs, ha⟩), rfl⟩))
  have hmem : ∀ (c : Config) (st r : List Entry) (e : Entry), e ∈ gen g c st r →
      e ∈ r ∨ ∃ s ∈ st, absent r s = true ∧ adjust c s = e := by
    intro c st r e h
    simp only [gen, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨s, hs, rfl⟩
    · exact Or.inl h
    · have := List.mem_filter.1 ((hg _ _).1 hs)
      exact Or.inr ⟨s, this.1, this.2, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c st r s hs ha
    exact ⟨adjust c s, hback c st r s hs ha, (hid c s).1, (hid c s).2.1, (hid c s).2.2⟩
  · intro c st r e he hn
    rcases hmem c st r e he with h' | ⟨s, hs, ha, rfl⟩
    · exact absurd h' hn
    · exact ⟨s, hs, ha, (hid c s).1, (hid c s).2.1, (hid c s).2.2⟩
  · intro c st r s e hd hs ha he heid hada hmod
    rcases hmem c st r e he with h' | ⟨s', hs', ha', rfl⟩
    · exfalso
      have hh : hasId r s.id = true := by
        unfold hasId
        rw [List.any_eq_true]
        exact ⟨_, h', by simp [heid]⟩
      unfold absent at ha
      simp [hh] at ha
    · have hss : s' = s := by
        apply hdistinct st s' s hd hs' hs
        rw [← (hid c s').1]
        exact heid
      subst hss
      exact hen c _
  · intro c st r s hs hi e he hn ⟨ea, em⟩
    rcases hmem c st r e he with h' | ⟨s', hs', ha', rfl⟩
    · exact hn h'
    · have hA : hasIdentity r s'.adapter s'.model = false := by
        unfold absent at ha'
        cases h2 : hasIdentity r s'.adapter s'.model
        · rfl
        · simp [h2] at ha'
      have h1 := (hid c s').2.1
      have h2 := (hid c s').2.2
      rw [h1] at ea
      rw [h2] at em
      rw [← ea, ← em, hA] at hi
      cases hi
  · intro c st r
    exact ⟨_, rfl⟩

/-- The first design. -/
def designA : SyncImpl := gen id

/-- The second design. -/
def designB : SyncImpl := gen List.reverse

/-- The input on which the two designs differ. -/
def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [⟨1, 0, 0, true⟩, ⟨2, 0, 1, true⟩]
def registry : List Entry := []

/-- The first design passes each law. -/
theorem a_passes : Passes designA := gen_passes id (fun _ _ => Iff.rfl)

/-- The second design passes each law. -/
theorem b_passes : Passes designB := gen_passes List.reverse (fun _ _ => List.mem_reverse)

/-- The input is legal: the starter list has no two entries with one id. -/
theorem starter_distinct : DistinctIds starter := by
  unfold DistinctIds starter
  simp

/-- The two designs give different registries. -/
theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
