/-
hardproof domain `swarm_policy`. AUTHOR FILE (pinned).

The mirror of `swarm_policy_table` in `harness/pilot_guards.py`.
-/
import Types

namespace HP

def ref : Impl := fun x =>
  if x.refusal then Output.solo
  else if x.launch then Output.explicit
  else if x.narrow then Output.solo
  else if x.broad then Output.broad
  else Output.solo

end HP
