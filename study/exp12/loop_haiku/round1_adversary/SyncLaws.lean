import Sync

/-! Laws for `puppetmaster models sync`, one law per stated requirement in
`DESCRIPTION.md`. A law is a statement about what a user observes. -/

namespace Sync

/-- "`--apply` appends the absent entries under the registry lock, with the
atomic writer. Each row that is in the file stays as it is: fields, key
order, position and unknown fields." (`DESCRIPTION.md`, item 2)
"It never changes an entry that is already in the file." (item 7)

The fields, key order and unknown fields of a file row are not in the model.
The model keeps each row at its index. -/
def RowsStay (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r : List Entry) (i : Nat), i < r.length → (f c st r)[i]? = r[i]?

/-- "New entries go to the end of the file." (`DESCRIPTION.md`, item 6)
"`--apply` appends the absent entries" (item 2). -/
def NewAtEnd (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r : List Entry), ∃ tail : List Entry, f c st r = r ++ tail

/-- "`models sync` adds only the entries that your registry lacks." (`DESCRIPTION.md`, item 5)
The registry lacks a starter when it has no row with its id and no row with its
adapter and model. -/
def AddsOnlyAbsent (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r tail : List Entry), f c st r = r ++ tail →
    ∀ e ∈ tail, ∃ s ∈ st, absent r s = true ∧
      e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "`--apply` appends the absent entries under the registry lock, with the
atomic writer." (`DESCRIPTION.md`, item 2)
"`puppetmaster models sync` lists the starter ids that the registry lacks,
for each adapter." (item 1) -/
def AddsEveryAbsent (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r tail : List Entry), f c st r = r ++ tail →
    ∀ s ∈ st, absent r s = true → ∃ e ∈ tail, e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- "A starter entry is not added when the registry has the same adapter and
model below a different id." (`DESCRIPTION.md`, item 4) -/
def NoSameIdentity (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r tail : List Entry), f c st r = r ++ tail →
    ∀ e ∈ tail, hasIdentity r e.adapter e.model = false

/-- "A new entry gets `enabled: false`, a `disabled_reason` that names
`puppetmaster models sync`, and `disabled_authority: models_sync`. Auto-routing
does not change. `--enable` keeps the starter state, but an entry on an adapter
that the platform lock disables always gets `enabled: false`."
(`DESCRIPTION.md`, item 3)

The model has the `enabled` flag only. The `disabled_reason` and
`disabled_authority` fields are not in the model. -/
def EnabledRule (f : SyncImpl) : Prop :=
  ∀ (c : Config) (st r tail : List Entry), f c st r = r ++ tail →
    ∀ e ∈ tail, ∃ s ∈ st, e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model ∧
      e.enabled = (c.enable && !c.locked s.adapter && s.enabled)

/-- The laws of the command. A design passes when it obeys every law. -/
def Passes (f : SyncImpl) : Prop :=
  RowsStay f ∧ NewAtEnd f ∧ AddsOnlyAbsent f ∧ AddsEveryAbsent f ∧
    NoSameIdentity f ∧ EnabledRule f

theorem ref_passes : Passes ref := by
  have hid : ∀ c s, (adjust c s).id = s.id := by
    intro c s; unfold adjust; split <;> rfl
  have had : ∀ c s, (adjust c s).adapter = s.adapter := by
    intro c s; unfold adjust; split <;> rfl
  have hmd : ∀ c s, (adjust c s).model = s.model := by
    intro c s; unfold adjust; split <;> rfl
  have hen : ∀ c s, (adjust c s).enabled = (c.enable && !c.locked s.adapter && s.enabled) := by
    intro c s
    cases hs : s.enabled <;> cases hc : c.enable <;> cases hl : c.locked s.adapter <;>
      simp [adjust, hs, hc, hl]
  have hcut : ∀ (c : Config) (st r tail : List Entry),
      ref c st r = r ++ tail → tail = (st.filter (absent r)).map (adjust c) := by
    intro c st r tail h
    have h' : r ++ (st.filter (absent r)).map (adjust c) = r ++ tail := h
    exact (List.append_cancel_left h').symm
  unfold Passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r i hi
    show (r ++ (st.filter (absent r)).map (adjust c))[i]? = r[i]?
    exact List.getElem?_append_left hi
  · intro c st r
    exact ⟨(st.filter (absent r)).map (adjust c), rfl⟩
  · intro c st r tail h e he
    rw [hcut c st r tail h] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, hab⟩ := List.mem_filter.mp ha
    exact ⟨a, hs, hab, hid c a, had c a, hmd c a⟩
  · intro c st r tail h s hs hab
    refine ⟨adjust c s, ?_, hid c s, had c s, hmd c s⟩
    rw [hcut c st r tail h]
    exact List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hab⟩, rfl⟩
  · intro c st r tail h e he
    rw [hcut c st r tail h] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨_, hab⟩ := List.mem_filter.mp ha
    simp only [absent, Bool.and_eq_true, Bool.not_eq_true'] at hab
    simpa [had, hmd] using hab.2
  · intro c st r tail h e he
    rw [hcut c st r tail h] at he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, _⟩ := List.mem_filter.mp ha
    exact ⟨a, hs, hid c a, had c a, hmd c a, hen c a⟩

theorem some_design_fails : ∃ f : SyncImpl, ¬ Passes f := by
  refine ⟨fun _ _ r => r, ?_⟩
  intro h
  unfold Passes at h
  obtain ⟨_, _, _, hEvery, _, _⟩ := h
  obtain ⟨e, he, _⟩ := hEvery { locked := fun _ => false, enable := false }
    [⟨0, 0, 0, true⟩] [] [] rfl ⟨0, 0, 0, true⟩ (List.mem_singleton_self _)
    (by simp [absent, hasId, hasIdentity])
  simp at he

end Sync
