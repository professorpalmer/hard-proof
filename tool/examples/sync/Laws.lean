/-
hardproof domain `sync`. AUTHOR FILE (pinned).

The seven natural laws of `DESCRIPTION.md`. There is no law for the order of
the new rows: the documentation does not say it.
-/
import Types

namespace HP

/-- Sentences 2 and 7: "Each row that is in the file stays as it is: fields,
key order, position and unknown fields." and "It never changes an entry that
is already in the file." The old registry is the start of the new registry.
With sentence 6 ("New entries go to the end of the file") this also says that
the new rows come after the old rows. -/
def KeepsRows (f : Impl) : Prop :=
  ∀ x, x.registry <+: f x

/-- Sentence 5: "`models sync` adds only the entries that your registry lacks."
Each added row is a starter entry that the registry lacks, with its id,
adapter and model. -/
def AddsOnlyAbsent (f : Impl) : Prop :=
  ∀ x, ∀ e ∈ added f x,
    ∃ s ∈ x.starter, absent x.registry s = true ∧ e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- Sentence 1: "`puppetmaster models sync` lists the starter ids that the
registry lacks, for each adapter." Each starter entry that the registry lacks
is added. -/
def AddsAllAbsent (f : Impl) : Prop :=
  ∀ x, Legal x → ∀ s ∈ x.starter, absent x.registry s = true →
    ∃ e ∈ added f x, e.id = s.id ∧ e.adapter = s.adapter ∧ e.model = s.model

/-- Sentence 4: "A starter entry is not added when the registry has the same
adapter and model below a different id." -/
def NoSameIdentity (f : Impl) : Prop :=
  ∀ x, ∀ e ∈ added f x, hasIdentity x.registry e.adapter e.model = false

/-- Sentence 3: "A new entry gets `enabled: false`" and "Auto-routing does not
change." Without `--enable`, each new entry is disabled. -/
def DisabledByDefault (f : Impl) : Prop :=
  ∀ x, x.enable = false → ∀ e ∈ added f x, e.enabled = false

/-- Sentence 3: "an entry on an adapter that the platform lock disables always
gets `enabled: false`." -/
def LockedDisabled (f : Impl) : Prop :=
  ∀ x, ∀ e ∈ added f x, isLocked x e.adapter = true → e.enabled = false

/-- Sentence 3: "`--enable` keeps the starter state." With `--enable`, a new
entry on an adapter that the lock does not disable has the `enabled` flag of
its starter entry. -/
def EnableKeepsState (f : Impl) : Prop :=
  ∀ x, Legal x → x.enable = true → ∀ e ∈ added f x, isLocked x e.adapter = false →
    ∃ s ∈ x.starter, absent x.registry s = true ∧ e.id = s.id ∧ e.enabled = s.enabled

def Passes (f : Impl) : Prop :=
  KeepsRows f ∧ AddsOnlyAbsent f ∧ AddsAllAbsent f ∧ NoSameIdentity f ∧
  DisabledByDefault f ∧ LockedDisabled f ∧ EnableKeepsState f

theorem some_design_fails : ∃ f : Impl, ¬ Passes f := by
  refine ⟨fun x => x.registry, ?_⟩
  intro hp
  have h := hp.2.2.1 ⟨false, [], [⟨1, 1, 1, false⟩], []⟩ rfl ⟨1, 1, 1, false⟩
    (by simp) (by simp [absent, hasId, hasIdentity])
  obtain ⟨e, he, _⟩ := h
  simp [added] at he

end HP
