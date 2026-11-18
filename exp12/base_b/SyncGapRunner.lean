/-
Hard Proof, experiment 12. HUMAN-OWNED FILE.

Prints the question for the human: the input, the registry that each of the
two designs gives, and the registry that the shipped code (`ref`) gives.
-/
import Sync
import SyncGapSolution

open Sync

def showRows (rows : List Entry) : String :=
  "; ".intercalate (rows.map fun e =>
    s!"id {e.id} (adapter {e.adapter}, model {e.model}, {if e.enabled then "enabled" else "disabled"})")

def main : IO Unit := do
  let c := SyncGap.config
  let adapters := ((SyncGap.starter ++ SyncGap.registry).map (·.adapter)).eraseDups
  IO.println s!"input: enable_flag={c.enable} locked_adapters={adapters.filter c.locked}"
  IO.println s!"input: starter=[{showRows SyncGap.starter}]"
  IO.println s!"input: registry=[{showRows SyncGap.registry}]"
  IO.println s!"design A result: [{showRows (SyncGap.designA c SyncGap.starter SyncGap.registry)}]"
  IO.println s!"design B result: [{showRows (SyncGap.designB c SyncGap.starter SyncGap.registry)}]"
  IO.println s!"shipped code: [{showRows (ref c SyncGap.starter SyncGap.registry)}]"
