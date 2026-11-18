/-
hardproof domain `sync`. AUTHOR FILE (pinned).

`ref` is the mirror of the shipped code. A law must not name `ref` or `adjust`.
-/
import Types

namespace HP

/-- `_synced_spec` in the Python code. -/
def adjust (x : Input) (s : Entry) : Entry :=
  if !s.enabled || (x.enable && !isLocked x s.adapter) then s else { s with enabled := false }

/-- `plan_starter_sync` plus the append in `sync_starter_registry`. -/
def ref : Impl :=
  fun x => x.registry ++ (x.starter.filter (absent x.registry)).map (adjust x)

end HP
