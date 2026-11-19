import Sync

/-!
Laws of `puppetmaster models sync --apply`, written from `DESCRIPTION.md`.

A law talks about the new registry `f c st r`. The rows after the old
registry `r` are the new entries `t` (law `KeepsPrefix` says that the result
is `r ++ t`).
-/

namespace Sync

/-- Two entries have one execution identity and one id. -/
def SameRow (s e : Entry) : Prop :=
  e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- Sentence 2: "Each row that is in the file stays as it is: fields, key
order, position and unknown fields."
Sentence 6: "New entries go to the end of the file."
The old registry is a prefix of the new registry. -/
def KeepsPrefix (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∃ t, f c st r = r ++ t

/-- Sentence 7: "It never changes an entry that is already in the file."
Each old row is in the new registry. -/
def KeepsRows (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ e ∈ r, e ∈ f c st r

/-- Sentence 5: "`models sync` adds only the entries that your registry lacks."
Sentence 4: "A starter entry is not added when the registry has the same
adapter and model below a different id."
Each new entry comes from a starter entry that the old registry lacks. -/
def AddsOnlyAbsent (f : SyncImpl) : Prop :=
  ∀ c st r t, DistinctIds st → f c st r = r ++ t →
    ∀ e ∈ t, ∃ s ∈ st, absent r s = true ∧ SameRow s e

/-- Sentence 2: "`--apply` appends the absent entries under the registry lock,
with the atomic writer."
Each starter entry that the old registry lacks is in the new entries. -/
def AddsAllAbsent (f : SyncImpl) : Prop :=
  ∀ c st r t, DistinctIds st → f c st r = r ++ t →
    ∀ s ∈ st, absent r s = true → ∃ e ∈ t, SameRow s e

/-- Sentence 3: "A new entry gets `enabled: false`, a `disabled_reason` that
names `puppetmaster models sync`, and `disabled_authority: models_sync`."
Without `--enable`, each new entry is disabled. -/
def NewDisabled (f : SyncImpl) : Prop :=
  ∀ c st r t, DistinctIds st → c.enable = false → f c st r = r ++ t →
    ∀ e ∈ t, e.enabled = false

/-- Sentence 3: "`--enable` keeps the starter state, but an entry on an adapter
that the platform lock disables always gets `enabled: false`."
A new entry on a locked adapter is disabled. -/
def LockedDisabled (f : SyncImpl) : Prop :=
  ∀ c st r t, DistinctIds st → f c st r = r ++ t →
    ∀ e ∈ t, c.locked e.adapter = true → e.enabled = false

/-- Sentence 3: "`--enable` keeps the starter state, but an entry on an adapter
that the platform lock disables always gets `enabled: false`."
With `--enable`, a new entry on an unlocked adapter has the state of its
starter entry. -/
def EnableKeepsState (f : SyncImpl) : Prop :=
  ∀ c st r t, DistinctIds st → c.enable = true → f c st r = r ++ t →
    ∀ e ∈ t, ∀ s ∈ st, s.id = e.id → c.locked s.adapter = false →
      e.enabled = s.enabled

/-- The new entries keep the order of the starter list: the ids of the new
entries, read in order, are a subsequence of the ids of the starter list. -/
def KeepsStarterOrder (f : SyncImpl) : Prop :=
  ∀ c st r t, DistinctIds st → f c st r = r ++ t →
    List.Sublist (t.map Entry.id) (st.map Entry.id)

/-- The conjunction of the laws. -/
def Passes (f : SyncImpl) : Prop :=
  KeepsPrefix f ∧ KeepsRows f ∧ AddsOnlyAbsent f ∧ AddsAllAbsent f ∧
  NewDisabled f ∧ LockedDisabled f ∧ EnableKeepsState f ∧
  KeepsStarterOrder f

theorem ref_passes : Passes ref := by
  have adjust_id : ∀ (c : Config) (s : Entry), (adjust c s).id = s.id := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_adapter : ∀ (c : Config) (s : Entry), (adjust c s).adapter = s.adapter := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_model : ∀ (c : Config) (s : Entry), (adjust c s).model = s.model := by
    intro c s; unfold adjust; split <;> rfl
  have ref_tail : ∀ {c st r t}, ref c st r = r ++ t →
      t = (st.filter (absent r)).map (adjust c) := by
    intro c st r t h
    unfold ref at h
    exact (List.append_cancel_left h).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r _ e he
    unfold ref
    exact List.mem_append_left _ he
  · intro c st r t _ h e he
    rw [ref_tail h] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, ha⟩ := List.mem_filter.mp hs
    exact ⟨s, hs, ha, adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r t _ h s hs ha
    rw [ref_tail h]
    exact ⟨adjust c s, List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ha⟩, rfl⟩,
      adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r t _ hc h e he
    rw [ref_tail h] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
    unfold adjust
    cases hs : s.enabled <;> simp [hs, hc]
  · intro c st r t _ h e he hl
    rw [ref_tail h] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
    rw [adjust_adapter] at hl
    unfold adjust
    cases hs : s.enabled <;> simp [hs, hl]
  · intro c st r t hd hc h e he s' hs' hid hl
    rw [ref_tail h] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    have hs := (List.mem_filter.mp hs).1
    rw [adjust_id] at hid
    have : s' = s := hd s' hs' s hs hid
    subst this
    unfold adjust
    cases he2 : s'.enabled <;> simp [he2, hc, hl]
  · intro c st r t _ h
    rw [ref_tail h, List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext (adjust_id c)
    rw [this]
    exact (List.filter_sublist).map _

/-- A design that never adds a row breaks `AddsAllAbsent`. -/
theorem some_design_fails : ∃ f : SyncImpl, ¬ Passes f := by
  refine ⟨fun _ _ r => r, ?_⟩
  intro hp
  have hd : DistinctIds [⟨0, 0, 0, true⟩] := by
    intro s hs s' hs' _
    simp at hs hs'
    rw [hs, hs']
  obtain ⟨e, he, _⟩ := hp.2.2.2.1 ⟨fun _ => false, false⟩ [⟨0, 0, 0, true⟩] [] [] hd rfl
    ⟨0, 0, 0, true⟩ (by simp) (by decide)
  simp at he

end Sync
