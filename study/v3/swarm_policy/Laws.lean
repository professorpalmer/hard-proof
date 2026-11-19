/-
hardproof domain `swarm_policy`. Laws from the order that the owner approved
(sentence 4 of DESCRIPTION.md). One law for each clause of that sentence.
-/
import Types

namespace HP

/-- "refusal gives solo with no mandate" -/
def RefusalWins (f : Impl) : Prop :=
  ∀ x : Input, x.refusal = true → f x = Output.solo

/-- "else launch gives explicit" -/
def LaunchIsExplicit (f : Impl) : Prop :=
  ∀ x : Input, x.refusal = false → x.launch = true → f x = Output.explicit

/-- "else narrow gives solo" -/
def NarrowIsSolo (f : Impl) : Prop :=
  ∀ x : Input, x.refusal = false → x.launch = false → x.narrow = true → f x = Output.solo

/-- "else broad gives broad" -/
def BroadIsBroad (f : Impl) : Prop :=
  ∀ x : Input, x.refusal = false → x.launch = false → x.narrow = false → x.broad = true →
    f x = Output.broad

/-- "else solo" -/
def DefaultIsSolo (f : Impl) : Prop :=
  ∀ x : Input, x.refusal = false → x.launch = false → x.narrow = false → x.broad = false →
    f x = Output.solo

def Passes (f : Impl) : Prop :=
  RefusalWins f ∧ LaunchIsExplicit f ∧ NarrowIsSolo f ∧ BroadIsBroad f ∧ DefaultIsSolo f

theorem some_design_fails : ∃ f : Impl, ¬ Passes f :=
  ⟨fun _ => Output.broad, fun h => by
    have := h.1 ⟨true, false, false, false⟩ rfl
    cases this⟩

end HP
