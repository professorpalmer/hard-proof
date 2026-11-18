-- hardproof: TOOL-OWNED FILE. The tool writes it again before each check.
-- Prints the question of an accepted conflict certificate, one `key<TAB>value` line each.
import Types
import Ref
import Codec
import ConflictSolution

open HP

def main : IO Unit := do
  let x := HPConflict.input
  IO.println s!"input_encoded\t{encodeInput x}"
  IO.println s!"input_shown\t{showInput x}"
  IO.println s!"ref_encoded\t{encodeOutput (ref x)}"
  IO.println s!"ref_shown\t{showOutput (ref x)}"
