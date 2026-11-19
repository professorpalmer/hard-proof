/-
Hard Proof, experiment 8. HUMAN-OWNED FILE.

Prints the question for the human: the input, and the registry that each of
the two designs gives. Run it only after the gap gate accepts.
-/
import SyncLaws
import SyncGapSolution

open SyncLaws

def showRows (rows : List Entry) : String :=
  "; ".intercalate (rows.map fun e =>
    s!"id {e.id} (adapter {e.adapter}, model {e.model}, {if e.enabled then "enabled" else "disabled"})")

def main : IO Unit := do
  let c := SyncGap.config
  let adapters := ((SyncGap.starter ++ SyncGap.registry).map (·.adapter)).eraseDups
  IO.println s!"enable_flag={c.enable} locked_adapters={adapters.filter c.locked}"
  IO.println s!"starter=[{showRows SyncGap.starter}]"
  IO.println s!"registry=[{showRows SyncGap.registry}]"
  IO.println s!"A_result=[{showRows (SyncGap.designA c SyncGap.starter SyncGap.registry)}]"
  IO.println s!"B_result=[{showRows (SyncGap.designB c SyncGap.starter SyncGap.registry)}]"
