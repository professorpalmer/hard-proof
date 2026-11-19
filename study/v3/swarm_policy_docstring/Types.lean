/-
hardproof domain `swarm_policy`. AUTHOR FILE (pinned).

The swarm policy of one user message in Marionette, as a function of four
signals. The real code is `harness.pilot_guards.swarm_policy_table`.
-/

namespace HP

/-- The four signals that the text rules give for one message. -/
structure Input where
  /-- The last delegation clause declines workers. -/
  refusal : Bool
  /-- A clause asks for a swarm. -/
  launch : Bool
  /-- The message asks a narrow question. -/
  narrow : Bool
  /-- The message asks for a broad audit or a platform contrast. -/
  broad : Bool
deriving DecidableEq, Repr

/-- What the pilot is told for the turn. -/
inductive Output where
  | solo
  | explicit
  | broad
deriving DecidableEq, Repr

abbrev Impl := Input → Output

/-- Each combination of the four signals is a legal input. -/
def legal : Input → Bool := fun _ => true

def Legal (x : Input) : Prop := legal x = true

end HP
