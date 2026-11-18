import Sync

namespace Sync

/-- "`--apply` appends the absent entries under the registry lock, with the atomic writer."
Every starter entry that the registry lacks has an entry in the result with the same id, adapter and model. -/
def AppendsAbsent (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r : List Entry) (s : Entry),
    s ∈ st → absent r s = true →
    ∃ e ∈ f c st r, e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "`models sync` adds only the entries that your registry lacks."
Every entry that is not in the registry has the id, adapter and model of a starter entry that the registry lacks. -/
def OnlyLacking (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r : List Entry) (e : Entry),
    e ∈ f c st r → e ∉ r →
    ∃ s ∈ st, absent r s = true ∧ e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "A new entry gets `enabled: false`, a `disabled_reason` that names `puppetmaster models sync`,
and `disabled_authority: models_sync`. Auto-routing does not change. `--enable` keeps the starter
state, but an entry on an adapter that the platform lock disables always gets `enabled: false`."
The model has no other field than `enabled`. An entry for a lacking starter entry is enabled only
when the starter is enabled, `--enable` is set and the platform lock does not disable its adapter. -/
def NewEntryEnabled (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r : List Entry) (s e : Entry),
    DistinctIds st → s ∈ st → absent r s = true → e ∈ f c st r →
    e.id = s.id → e.adapter = s.adapter → e.model = s.model →
    e.enabled = (s.enabled && c.enable && !c.locked s.adapter)

/-- "A starter entry is not added when the registry has the same adapter and model below a different id."
If the registry has a row with the adapter and model of a starter entry, no new entry has that adapter and model. -/
def NotAddedByIdentity (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r : List Entry) (s : Entry),
    s ∈ st → hasIdentity r s.adapter s.model = true →
    ∀ e ∈ f c st r, e ∉ r → ¬ (e.adapter = s.adapter ∧ e.model = s.model)

/-- "Each row that is in the file stays as it is: fields, key order, position and unknown fields."
"New entries go to the end of the file." "It never changes an entry that is already in the file."
The registry is a prefix of the result. -/
def RowsKept (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r : List Entry), ∃ rest, f c st r = r ++ rest

/-- The owner decided: the new entries go after the registry in starter order, one for each
lacking starter entry. The ids of the rows after the registry are the ids of the starter
entries that the registry lacks, in the order of the starter list. -/
def NewEntriesInStarterOrder (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r rest : List Entry),
    f c st r = r ++ rest →
    rest.map (fun e => e.id) = (st.filter (absent r)).map (fun s => s.id)

/-- A design passes when it obeys every law. -/
def Passes (f : SyncImpl) : Prop :=
  AppendsAbsent f ∧ OnlyLacking f ∧ NewEntryEnabled f ∧ NotAddedByIdentity f ∧ RowsKept f
    ∧ NewEntriesInStarterOrder f

theorem ref_passes : Passes ref := by
  unfold Passes AppendsAbsent OnlyLacking NewEntryEnabled NotAddedByIdentity RowsKept
    NewEntriesInStarterOrder
  have hid : ∀ (c : Config) (s : Entry),
      (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
    intro c s
    unfold adjust
    split <;> simp
  have hen : ∀ (c : Config) (s : Entry),
      (adjust c s).enabled = (s.enabled && c.enable && !c.locked s.adapter) := by
    intro c s
    rcases c with ⟨lk, ce⟩
    rcases s with ⟨i, a, m, en⟩
    unfold adjust
    cases en <;> cases ce <;> cases hl : lk a <;> simp [hl]
  have hback : ∀ (c : Config) (st r : List Entry) (s : Entry),
      s ∈ st → absent r s = true → adjust c s ∈ ref c st r := by
    intro c st r s hs ha
    simp only [ref]
    exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, ha⟩, rfl⟩))
  have hmem : ∀ (c : Config) (st r : List Entry) (e : Entry), e ∈ ref c st r →
      e ∈ r ∨ ∃ s ∈ st, absent r s = true ∧ adjust c s = e := by
    intro c st r e h
    simp only [ref, List.mem_append, List.mem_map, List.mem_filter] at h
    rcases h with h | ⟨s, ⟨hs, ha⟩, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, ha, rfl⟩
  have hdistinct : ∀ (st : List Entry) (s t : Entry), DistinctIds st →
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro c st r rest h
    simp only [ref] at h
    have h2 := List.append_cancel_left h
    subst h2
    simp [List.map_map, Function.comp_def, (hid c _).1]

theorem some_design_fails : ∃ f : SyncImpl, ¬ Passes f := by
  refine ⟨fun _ _ r => r, ?_⟩
  intro h
  unfold Passes AppendsAbsent at h
  have hs : (⟨0, 0, 0, true⟩ : Entry) ∈ [⟨0, 0, 0, true⟩] := List.mem_singleton_self _
  obtain ⟨e, he, _⟩ := h.1 ⟨fun _ => false, false⟩ [⟨0, 0, 0, true⟩] [] ⟨0, 0, 0, true⟩ hs (by decide)
  simp at he

end Sync
