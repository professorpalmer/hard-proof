/-
hardproof domain `clamp`. AUTHOR FILE (pinned).

`ref` is the mirror of `pycode/clampmod.py`.
-/
import Types

namespace HP

def ref : Impl := fun i =>
  if i.x < i.lo then i.lo
  else if i.x > i.hi then i.hi
  else i.x

end HP
