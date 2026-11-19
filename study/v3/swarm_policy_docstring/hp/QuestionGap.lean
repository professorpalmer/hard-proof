-- hardproof: TOOL-OWNED FILE. The tool writes it again before each check.
-- Prints the question of an accepted gap certificate, one `key<TAB>value` line each.
import Types
import Ref
import Codec
import GapSolution

open HP

def main : IO Unit := do
  let x := HPGap.input
  IO.println s!"input_encoded\t{encodeInput x}"
  IO.println s!"input_shown\t{showInput x}"
  IO.println s!"a_encoded\t{encodeOutput (HPGap.designA x)}"
  IO.println s!"a_shown\t{showOutput (HPGap.designA x)}"
  IO.println s!"b_encoded\t{encodeOutput (HPGap.designB x)}"
  IO.println s!"b_shown\t{showOutput (HPGap.designB x)}"
  IO.println s!"ref_encoded\t{encodeOutput (ref x)}"
  IO.println s!"ref_shown\t{showOutput (ref x)}"
