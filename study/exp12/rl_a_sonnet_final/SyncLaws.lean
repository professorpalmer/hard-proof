import Sync

namespace Sync

/-- "Each row that is in the file stays as it is: fields, key order, position
and unknown fields." and "It never changes an entry that is already in the
file." and "New entries go to the end of the file."
The old registry is a prefix of the new one. -/
def KeepsExisting (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∃ new, f c st r = r ++ new

/-- "`models sync` adds only the entries that your registry lacks."
Each new row comes from a starter entry that the registry lacks, with its
id, adapter and model. -/
def AddsOnlyAbsent (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ x ∈ f c st r, x ∉ r →
    ∃ s ∈ st, absent r s = true ∧ x.id = s.id ∧ x.adapter = s.adapter ∧ x.model = s.model

/-- "`puppetmaster models sync` lists the starter ids that the registry lacks"
and "`--apply` appends the absent entries".
Each absent starter entry gets a row in the new registry. -/
def AddsAllAbsent (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ s ∈ st, absent r s = true →
    ∃ x ∈ f c st r, x.id = s.id ∧ x.adapter = s.adapter ∧ x.model = s.model

/-- "A starter entry is not added when the registry has the same adapter and
model below a different id." No new row has an adapter and model that the
registry already has. -/
def NoSameIdentity (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ x ∈ f c st r, x ∉ r →
    hasIdentity r x.adapter x.model = false

/-- "A new entry gets `enabled: false`" and "Auto-routing does not change."
Without `--enable`, a new row is disabled. -/
def NewDisabledByDefault (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → c.enable = false →
    ∀ s ∈ st, absent r s = true → ∀ x ∈ f c st r, x.id = s.id → x.enabled = false

/-- "`--enable` keeps the starter state". With `--enable`, on an adapter that
the platform lock does not disable, a new row has the enabled flag of its
starter entry. -/
def EnableKeepsStarter (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → c.enable = true →
    ∀ s ∈ st, absent r s = true → c.locked s.adapter = false →
      ∀ x ∈ f c st r, x.id = s.id → x.enabled = s.enabled

/-- "an entry on an adapter that the platform lock disables always gets
`enabled: false`". -/
def LockedAlwaysDisabled (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st →
    ∀ s ∈ st, absent r s = true → c.locked s.adapter = true →
      ∀ x ∈ f c st r, x.id = s.id → x.enabled = false

/-- The owner's answer: new rows follow the order of the starter list.
The new rows are the old registry, then a part of the starter list in starter
order. No starter entry gives two rows. -/
def NewInStarterOrder (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∃ new, f c st r = r ++ new ∧
    List.Sublist (new.map Entry.id) (st.map Entry.id)

/-- The owner's answer: a row that is already in the registry is not added
again. When the new registry is the old one followed by new rows, no new row
has an id that the registry already has. -/
def NoDuplicateOfExisting (f : SyncImpl) : Prop :=
  ∀ c st r, DistinctIds st → ∀ new, f c st r = r ++ new →
    ∀ x ∈ new, hasId r x.id = false

def Passes (f : SyncImpl) : Prop :=
  KeepsExisting f ∧ AddsOnlyAbsent f ∧ AddsAllAbsent f ∧ NoSameIdentity f ∧
  NewDisabledByDefault f ∧ EnableKeepsStarter f ∧ LockedAlwaysDisabled f ∧
  NewInStarterOrder f ∧ NoDuplicateOfExisting f

theorem ref_passes : Passes ref := by
  have adj_id : ∀ c s, (adjust c s).id = s.id := by
    intro c s; simp [adjust]; split <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r _
    exact ⟨_, rfl⟩
  · intro c st r _ x hx hxr
    simp only [ref, List.mem_append, List.mem_map, List.mem_filter] at hx
    rcases hx with h | ⟨s, ⟨hs, ha⟩, rfl⟩
    · exact absurd h hxr
    · exact ⟨s, hs, ha, by simp [adjust]; split <;> simp, by simp [adjust]; split <;> simp,
        by simp [adjust]; split <;> simp⟩
  · intro c st r _ s hs ha
    refine ⟨adjust c s, ?_, ?_⟩
    · simp only [ref, List.mem_append, List.mem_map, List.mem_filter]
      exact Or.inr ⟨s, ⟨hs, ha⟩, rfl⟩
    · simp [adjust]; split <;> simp
  · intro c st r _ x hx hxr
    simp only [ref, List.mem_append, List.mem_map, List.mem_filter] at hx
    rcases hx with h | ⟨s, ⟨hs, ha⟩, rfl⟩
    · exact absurd h hxr
    · have : (adjust c s).adapter = s.adapter := by simp [adjust]; split <;> simp
      have h2 : (adjust c s).model = s.model := by simp [adjust]; split <;> simp
      rw [this, h2]
      simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      simpa using ha.2
  · intro c st r hd he s hs ha x hx hid
    simp only [ref, List.mem_append, List.mem_map, List.mem_filter] at hx
    rcases hx with h | ⟨s', ⟨hs', ha'⟩, rfl⟩
    · simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      have : hasId r s.id = true := by
        simp only [hasId, List.any_eq_true, beq_iff_eq]
        exact ⟨x, h, hid⟩
      simp [ha.1] at this
    · simp only [adjust, he]; split <;> simp_all
  · intro c st r hd he s hs ha hl x hx hid
    simp only [ref, List.mem_append, List.mem_map, List.mem_filter] at hx
    rcases hx with h | ⟨s', ⟨hs', ha'⟩, rfl⟩
    · simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      have : hasId r s.id = true := by
        simp only [hasId, List.any_eq_true, beq_iff_eq]
        exact ⟨x, h, hid⟩
      simp [ha.1] at this
    · have : s' = s := hd s' hs' s hs (by rw [← adj_id c s']; exact hid)
      subst this
      simp only [adjust, he, hl]; split <;> simp_all
  · intro c st r hd s hs ha hl x hx hid
    simp only [ref, List.mem_append, List.mem_map, List.mem_filter] at hx
    rcases hx with h | ⟨s', ⟨hs', ha'⟩, rfl⟩
    · simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
      have : hasId r s.id = true := by
        simp only [hasId, List.any_eq_true, beq_iff_eq]
        exact ⟨x, h, hid⟩
      simp [ha.1] at this
    · have : s' = s := hd s' hs' s hs (by rw [← adj_id c s']; exact hid)
      subst this
      simp only [adjust]; split <;> simp_all
  · intro c st r _
    refine ⟨_, rfl, ?_⟩
    rw [List.map_map]
    have : (Entry.id ∘ adjust c) = Entry.id := funext (adj_id c)
    rw [this]
    exact (List.filter_sublist).map _
  · intro c st r _ new hnew x hx
    have h1 : new = (st.filter (absent r)).map (adjust c) :=
      (List.append_cancel_left (as := r) (by simpa [ref] using hnew.symm))
    subst h1
    simp only [List.mem_map, List.mem_filter] at hx
    obtain ⟨s, ⟨_, ha⟩, rfl⟩ := hx
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at ha
    rw [adj_id]; exact ha.1

theorem some_design_fails : ∃ f : SyncImpl, ¬ Passes f := by
  refine ⟨fun _ _ r => r, ?_⟩
  intro h
  have h3 := h.2.2.1
  have := h3 ⟨fun _ => false, false⟩ [⟨1, 1, 1, false⟩] [] (by
    intro s hs s' hs' _
    simp at hs hs'; subst hs; subst hs'; rfl) ⟨1, 1, 1, false⟩ (by simp)
    (by simp [absent, hasId, hasIdentity])
  simp at this

end Sync
