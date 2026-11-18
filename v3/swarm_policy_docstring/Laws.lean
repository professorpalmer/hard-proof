/-
hardproof domain `swarm_policy`, with the docstring as the only source.
The docstring states one requirement: "A refusal always wins."
-/
import Types

namespace HP

/-- "A refusal always wins." -/
def RefusalWins (f : Impl) : Prop :=
  ∀ x : Input, x.refusal = true → f x = Output.solo

def Passes (f : Impl) : Prop := RefusalWins f

theorem some_design_fails : ∃ f : Impl, ¬ Passes f :=
  ⟨fun _ => Output.broad, fun h => by
    have := h ⟨true, false, false, false⟩ rfl
    cases this⟩

end HP
