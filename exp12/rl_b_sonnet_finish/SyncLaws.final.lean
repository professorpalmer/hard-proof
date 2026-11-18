import Sync

namespace Sync

/-- The rows that a run adds: the result without the old registry rows. -/
def added (f : SyncImpl) (c : Config) (st r : List Entry) : List Entry :=
  (f c st r).drop r.length

/-- "Each row that is in the file stays as it is: fields, key order, position
and unknown fields." and "It never changes an entry that is already in the
file." The old registry is the start of the new registry. -/
def KeepsRows (f : SyncImpl) : Prop :=
  ∀ c st r, r <+: f c st r

/-- "`models sync` adds only the entries that your registry lacks." Each added
row is a starter entry that the registry lacks, with its id, adapter and model. -/
def AddsOnlyAbsent (f : SyncImpl) : Prop :=
  ∀ c st r, ∀ e ∈ added f c st r,
    ∃ s ∈ st, absent r s = true ∧ e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "`puppetmaster models sync` lists the starter ids that the registry lacks,
for each adapter." Each starter entry that the registry lacks is added. -/
def AddsAllAbsent (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ s ∈ st, absent r s = true →
    ∃ e ∈ added f c st r, e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "A starter entry is not added when the registry has the same adapter and
model below a different id." No added row has the adapter and model of a
registry row. -/
def NoSameIdentity (f : SyncImpl) : Prop :=
  ∀ c st r, ∀ e ∈ added f c st r, hasIdentity r e.adapter e.model = false

/-- "A new entry gets `enabled: false`" and "Auto-routing does not change."
Without `--enable`, each new entry is disabled. -/
def DisabledByDefault (f : SyncImpl) : Prop :=
  ∀ c st r, c.enable = false → ∀ e ∈ added f c st r, e.enabled = false

/-- "an entry on an adapter that the platform lock disables always gets
`enabled: false`." This holds with or without `--enable`. -/
def LockedDisabled (f : SyncImpl) : Prop :=
  ∀ c st r, ∀ e ∈ added f c st r, c.locked e.adapter = true → e.enabled = false

/-- "`--enable` keeps the starter state." With `--enable`, a new entry on an
adapter that the lock does not disable has the `enabled` flag of its starter entry. -/
def EnableKeepsState (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → c.enable = true → ∀ e ∈ added f c st r,
    c.locked e.adapter = false →
    ∃ s ∈ st, absent r s = true ∧ e.id = s.id ∧ e.enabled = s.enabled

/-- "New entries go to the end of the file." The new registry is the old
registry followed by the added rows. -/
def NewAtEnd (f : SyncImpl) : Prop :=
  ∀ c st r, f c st r = r ++ added f c st r

/-- The added rows keep the order of the starter list: their ids are a
subsequence of the starter ids. -/
def StarterOrder (f : SyncImpl) : Prop :=
  ∀ c st r, ((added f c st r).map Entry.id).Sublist (st.map Entry.id)

def Passes (f : SyncImpl) : Prop :=
  KeepsRows f ∧ AddsOnlyAbsent f ∧ AddsAllAbsent f ∧ NoSameIdentity f ∧
  DisabledByDefault f ∧ LockedDisabled f ∧ EnableKeepsState f ∧ NewAtEnd f ∧
  StarterOrder f

theorem ref_passes : Passes ref := by
  have hadd : ∀ c st r, added ref c st r = (st.filter (absent r)).map (adjust c) := by
    intro c st r
    simp [added, ref]
  have hmem : ∀ c st r e, e ∈ added ref c st r →
      ∃ s ∈ st, absent r s = true ∧ adjust c s = e := by
    intro c st r e h
    rw [hadd] at h
    simp only [List.mem_map, List.mem_filter] at h
    obtain ⟨s, ⟨hs, ha⟩, he⟩ := h
    exact ⟨s, hs, ha, he⟩
  have hfld : ∀ c s, (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧
      (adjust c s).model = s.model := by
    intro c s
    unfold adjust
    split <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r
    exact ⟨_, rfl⟩
  · intro c st r e h
    obtain ⟨s, hs, ha, he⟩ := hmem c st r e h
    obtain ⟨h1, h2, h3⟩ := hfld c s
    subst he
    exact ⟨s, hs, ha, h1, h2, h3⟩
  · intro c st r _ s hs ha
    refine ⟨adjust c s, ?_, hfld c s⟩
    rw [hadd]
    exact List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, rfl⟩
  · intro c st r e h
    obtain ⟨s, hs, ha, he⟩ := hmem c st r e h
    obtain ⟨_, h2, h3⟩ := hfld c s
    subst he
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
    rw [h2, h3]
    simpa using ha.2
  · intro c st r hc e h
    obtain ⟨s, hs, ha, he⟩ := hmem c st r e h
    subst he
    unfold adjust
    split <;> simp_all
  · intro c st r e h hl
    obtain ⟨s, hs, ha, he⟩ := hmem c st r e h
    subst he
    have hl' : c.locked s.adapter = true := by rw [(hfld c s).2.1] at hl; exact hl
    unfold adjust
    split <;> simp_all
  · intro c st r _ hc e h hl
    obtain ⟨s, hs, ha, he⟩ := hmem c st r e h
    subst he
    refine ⟨s, hs, ha, (hfld c s).1, ?_⟩
    have hl' : c.locked s.adapter = false := by rw [(hfld c s).2.1] at hl; exact hl
    simp [adjust, hc, hl']
  · intro c st r
    rw [hadd]
    simp [ref]
  · intro c st r
    rw [hadd, List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext fun s => (hfld c s).1
    rw [this]
    exact (List.filter_sublist).map _

theorem some_design_fails : ∃ f : SyncImpl, ¬ Passes f := by
  refine ⟨fun _ _ r => r, ?_⟩
  intro hp
  have h := hp.2.2.1 ⟨fun _ => false, false⟩ [⟨1, 1, 1, false⟩] []
    (by simp [DistinctIds]) ⟨1, 1, 1, false⟩ (by simp) (by simp [absent, hasId, hasIdentity])
  obtain ⟨e, he, _⟩ := h
  simp [added] at he

end Sync
