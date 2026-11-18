import SyncLaws
import SyncSolution

open SyncLaws

namespace SyncGap

/-- The rows that the shipped code appends. -/
def base (c : Config) (st r : List Entry) : List Entry :=
  (st.filter (absent r)).map (adjust c)

/-- A design that appends `post` of the shipped rows. -/
def mk (post : List Entry → List Entry) : SyncImpl :=
  fun c st r => r ++ post (base c st r)

/-- `post` keeps the same members and maps the empty list to itself. -/
def Sound (post : List Entry → List Entry) : Prop :=
  (∀ x a, a ∈ post x ↔ a ∈ x) ∧ post [] = []

theorem hasId_iff (x : List Entry) (i : Nat) : hasId x i = true ↔ ∃ e ∈ x, e.id = i := by
  simp [hasId, List.any_eq_true]

theorem added_eq (post : List Entry → List Entry) (c : Config) (st r added : List Entry)
    (h : mk post c st r = r ++ added) : added = post (base c st r) :=
  (List.append_cancel_left (show r ++ post (base c st r) = r ++ added from h)).symm

theorem mk_passes (post : List Entry → List Entry) (hp : Sound post) : Passes (mk post) := by
  obtain ⟨hmem, hnil⟩ := hp
  have nothing : NothingLeft (mk post) := by
    intro c st r s hs ha
    have h := Sync.ref_nothing_left c st r s hs ha
    simp only [refSync, hasId, List.any_append, Bool.or_eq_true] at h
    show hasId (r ++ post (base c st r)) s.id = true
    simp only [hasId, List.any_append, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl h
    · right
      obtain ⟨e, he, hid⟩ := (hasId_iff _ _).mp h
      exact (hasId_iff _ _).mpr ⟨e, (hmem _ _).mpr he, hid⟩
  refine ⟨?_, ?_, nothing, ?_, ?_, ?_, ?_⟩
  · intro c st r; exact ⟨_, rfl⟩
  · intro c st r added h a ha
    rw [added_eq post c st r added h, hmem] at ha
    exact Sync.ref_only_absent_starter c st r _ rfl a ha
  · intro c st r added hen h a ha
    rw [added_eq post c st r added h, hmem] at ha
    exact Sync.ref_disabled_by_default c st r _ hen rfl a ha
  · intro c st r added h a ha
    rw [added_eq post c st r added h, hmem] at ha
    exact Sync.ref_locked_stays_disabled c st r _ rfl a ha
  · intro c st r added hd hen h a ha
    rw [added_eq post c st r added h, hmem] at ha
    exact Sync.ref_enable_keeps_starter_state c st r _ hd hen rfl a ha
  · intro c st r
    have hf : st.filter (absent (mk post c st r)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s hs hab
      have h1 := Sync.absent_append _ _ _ hab
      have h3 := nothing c st r s hs h1
      simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
      rw [hab.1] at h3
      exact absurd h3 (by simp)
    show mk post c st r ++ post (base c st (mk post c st r)) = mk post c st r
    simp only [base, hf, List.map_nil, hnil, List.append_nil]

/-- The first design: the shipped code. -/
def designA : SyncImpl := mk id

/-- The second design: it appends each new row twice. -/
def designB : SyncImpl := mk (fun x => x ++ x)

/-- The input on which the two designs differ. -/
def config : Config := { locked := fun _ => false, enable := false }
def starter : List Entry := [⟨1, 1, 1, true⟩]
def registry : List Entry := []

/-- The first design passes each law. -/
theorem a_passes : Passes designA :=
  mk_passes id ⟨fun _ _ => Iff.rfl, rfl⟩

/-- The second design passes each law. -/
theorem b_passes : Passes designB :=
  mk_passes (fun x => x ++ x) ⟨fun x a => by simp, rfl⟩

/-- The input is legal: the starter list has no two entries with one id. -/
theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  rw [hs, hs']

/-- The two designs give different registries. -/
theorem differ : designA config starter registry ≠ designB config starter registry := by
  decide

end SyncGap
