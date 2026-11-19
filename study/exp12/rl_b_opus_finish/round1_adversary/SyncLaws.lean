import Sync

namespace Sync

/-- The rows that a design puts after the old registry rows. -/
def added (f : SyncImpl) (c : Config) (st r : List Entry) : List Entry :=
  (f c st r).drop r.length

/-- "Each row that is in the file stays as it is: fields, key order, position
and unknown fields." and "It never changes an entry that is already in the
file." Each old row stays, with its fields, at its position. -/
def KeepsExistingRows (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → (f c st r).take r.length = r

/-- "New entries go to the end of the file." (also "`--apply` appends the
absent entries") The result is the old registry with new rows after it. -/
def NewEntriesAtEnd (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∃ n, f c st r = r ++ n

/-- "`puppetmaster models sync` lists the starter ids that the registry lacks,
for each adapter." and "`--apply` appends the absent entries". Each starter
entry that the registry lacks is added, with its id, adapter and model. -/
def AddsEachAbsent (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ s ∈ st, absent r s = true →
    ∃ e ∈ added f c st r, e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "`models sync` adds only the entries that your registry lacks." Each new
row is a starter entry that the registry lacks. -/
def AddsOnlyAbsent (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ e ∈ added f c st r,
    ∃ s ∈ st, absent r s = true ∧ e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "`--apply` appends the absent entries" and "`models sync` adds only the
entries that your registry lacks." Each absent entry is added one time: the
number of new rows is the number of absent starter entries. -/
def AddsEachOnce (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st →
    (added f c st r).length = (st.filter (absent r)).length

/-- "A starter entry is not added when the registry has the same adapter and
model below a different id." No new row has an adapter and model that the
registry already has. -/
def NoIdentityDuplicate (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ e ∈ added f c st r,
    hasIdentity r e.adapter e.model = false

/-- "A new entry gets `enabled: false`". Without `--enable`, each new row is
disabled. -/
def NewDisabledByDefault (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → c.enable = false →
    ∀ e ∈ added f c st r, e.enabled = false

/-- "`--enable` keeps the starter state". With `--enable`, a new row on an
adapter that the lock does not disable has the `enabled` value of its starter
entry. -/
def EnableKeepsStarterState (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → c.enable = true →
    ∀ s ∈ st, absent r s = true → c.locked s.adapter = false →
      ∀ e ∈ added f c st r, e.id = s.id → e.enabled = s.enabled

/-- "an entry on an adapter that the platform lock disables always gets
`enabled: false`." -/
def LockedAlwaysDisabled (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st →
    ∀ e ∈ added f c st r, c.locked e.adapter = true → e.enabled = false

/-- The new rows are in the order of the starter list: the ids of the new rows
are a subsequence of the ids of the starter entries, in the same order. -/
def NewRowsInStarterOrder (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st →
    List.Sublist ((added f c st r).map Entry.id) (st.map Entry.id)

/-- The conjunction of the laws. -/
def Passes (f : SyncImpl) : Prop :=
  KeepsExistingRows f ∧ NewEntriesAtEnd f ∧ AddsEachAbsent f ∧ AddsOnlyAbsent f ∧
  AddsEachOnce f ∧ NoIdentityDuplicate f ∧ NewDisabledByDefault f ∧
  EnableKeepsStarterState f ∧ LockedAlwaysDisabled f ∧
  NewRowsInStarterOrder f

theorem same_id {st : List Entry} (hd : DistinctIds st) {a b : Entry}
    (ha : a ∈ st) (hb : b ∈ st) (h : a.id = b.id) : a = b := by
  induction st with
  | nil => cases ha
  | cons x t ih =>
    have hd' := List.pairwise_cons.1 hd
    cases List.mem_cons.1 ha with
    | inl h1 =>
      cases List.mem_cons.1 hb with
      | inl h2 => rw [h1, h2]
      | inr h2 => exact absurd (h1 ▸ h) (hd'.1 b h2)
    | inr h1 =>
      cases List.mem_cons.1 hb with
      | inl h2 => exact absurd (h2 ▸ h.symm) (hd'.1 a h1)
      | inr h2 => exact ih hd'.2 h1 h2

theorem ref_passes : Passes ref := by
  have added_ref : ∀ (c : Config) (st r : List Entry),
      added ref c st r = (st.filter (absent r)).map (adjust c) := by
    intro c st r; simp [added, ref]
  have adjust_id : ∀ c s, (adjust c s).id = s.id := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_adapter : ∀ c s, (adjust c s).adapter = s.adapter := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_model : ∀ c s, (adjust c s).model = s.model := by
    intro c s; unfold adjust; split <;> rfl
  have adjust_enabled : ∀ c s,
      (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
    intro c s; unfold adjust
    cases h1 : s.enabled <;> cases c.enable <;> cases c.locked s.adapter <;> simp [h1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    simp [ref]
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r _ s hs ha
    rw [added_ref]
    refine ⟨adjust c s, ?_, adjust_id c s, adjust_adapter c s, adjust_model c s⟩
    exact List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, rfl⟩
  · intro c st r _ e he
    rw [added_ref] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    obtain ⟨hs, ha⟩ := List.mem_filter.1 hs
    exact ⟨s, hs, ha, adjust_id c s, adjust_adapter c s, adjust_model c s⟩
  · intro c st r _
    rw [added_ref, List.length_map]
  · intro c st r _ e he
    rw [added_ref] at he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    obtain ⟨_, ha⟩ := List.mem_filter.1 hs
    rw [adjust_adapter, adjust_model]
    simp [absent] at ha
    simpa using ha.2
  · intro c st r _ hc e he
    rw [added_ref] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 he
    simp [adjust_enabled, hc]
  · intro c st r hd hc s hs ha hl e he hid
    rw [added_ref] at he
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 he
    obtain ⟨hs', _⟩ := List.mem_filter.1 hs'
    rw [adjust_id] at hid
    have : s' = s := same_id hd hs' hs hid
    subst this
    simp [adjust_enabled, hc, hl]
  · intro c st r _ e he hl
    rw [added_ref] at he
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 he
    rw [adjust_adapter] at hl
    simp [adjust_enabled, hl]
  · intro c st r _
    rw [added_ref, List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext (adjust_id c)
    rw [this]
    exact List.Sublist.map _ (List.filter_sublist)

theorem some_design_fails : ∃ f : SyncImpl, ¬ Passes f := by
  refine ⟨fun _ _ _ => [], fun h => ?_⟩
  have := h.1 ⟨fun _ => false, false⟩ [] [⟨0, 0, 0, true⟩] List.Pairwise.nil
  simp at this

end Sync
