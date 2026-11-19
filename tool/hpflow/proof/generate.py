"""The tool-owned files under `hp/`.

The tool writes these files again before each check, so an edit to one of
them has no effect. A file is written only when its text changes.
"""
from __future__ import annotations

import json
from pathlib import Path

from hpflow.proof.domain import Domain

TOOLCHAIN = "leanprover/lean4:v4.36.0\n"
PERMITTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PACKAGE = "hardproof_domain"

HEADER = "-- hardproof: TOOL-OWNED FILE. The tool writes it again before each check.\n"

# kind -> (solution module, challenge module, config file, theorem names, definition names)
KINDS = {
    "ref": ("RefPassesSolution", "HPRefChallenge", "comparator_ref.json",
            ["HPRef.ref_passes"], []),
    "conflict": ("ConflictSolution", "HPConflictChallenge", "comparator_conflict.json",
                 ["HPConflict.input_legal", "HPConflict.ref_breaks"], ["HPConflict.input"]),
    "gap": ("GapSolution", "HPGapChallenge", "comparator_gap.json",
            ["HPGap.a_passes", "HPGap.b_passes", "HPGap.input_legal", "HPGap.differ"],
            ["HPGap.designA", "HPGap.designB", "HPGap.input"]),
    "complete": ("CompleteSolution", "HPCompleteChallenge", "comparator_complete.json",
                 ["HPComplete.laws_complete"], []),
}

# Generated at `check conflict` time, because the challenge names one law.
# These two files are not pinned.
CONFLICT_FILES = ["HPConflictChallenge.lean", "comparator_conflict.json"]


def lakefile() -> str:
    libs = [("HPModel", "..", ["Types", "Ref", "Codec"]), ("HPLaws", "..", ["Laws"])]
    for kind, (solution, challenge, _cfg, _t, _d) in KINDS.items():
        cap = kind.capitalize()
        libs.append((f"HP{cap}Challenge", ".", [challenge]))
        libs.append((f"HP{cap}Work", "..", [solution]))
    parts = [
        "# hardproof: TOOL-OWNED FILE. The tool writes it again before each check.",
        "# One lean_lib for each solution, so that a broken solution of one kind",
        "# does not stop the check of another kind.",
        f'name = "{PACKAGE}"',
        'defaultTargets = ["HPModel"]',
    ]
    for name, src, roots in libs:
        parts.append("")
        parts.append("[[lean_lib]]")
        parts.append(f'name = "{name}"')
        parts.append(f'srcDir = "{src}"')
        parts.append("roots = [" + ", ".join(f'"{r}"' for r in roots) + "]")
    return "\n".join(parts) + "\n"


def manifest() -> str:
    data = {"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [],
            "name": PACKAGE, "lakeDir": ".lake", "fixedToolchain": False}
    return json.dumps(data, indent=1) + "\n"


def comparator_config(kind: str) -> str:
    solution, challenge, _cfg, theorems, defs = KINDS[kind]
    data = {"challenge_module": challenge, "solution_module": solution,
            "theorem_names": theorems, "definition_names": defs,
            "permitted_axioms": PERMITTED_AXIOMS}
    return json.dumps(data, indent=2) + "\n"


def ref_challenge(ns: str) -> str:
    return HEADER + f"""import Types
import Ref
import Laws

open {ns}

namespace HPRef

/-- The mirror of the shipped code passes each law. -/
theorem ref_passes : Passes ref := sorry

end HPRef
"""


def conflict_challenge(ns: str, law: str) -> str:
    return HEADER + f"""-- hardproof-law: {law}
import Types
import Ref
import Laws

open {ns}

namespace HPConflict

/-- The witness input. -/
def input : Input := sorry

/-- The witness input is legal. -/
theorem input_legal : Legal input := sorry

/-- The mirror of the shipped code breaks the law `{law}`. -/
theorem ref_breaks : ¬ {law} ref := sorry

end HPConflict
"""


def gap_challenge(ns: str) -> str:
    return HEADER + f"""import Types
import Laws

open {ns}

namespace HPGap

/-- The first design. -/
def designA : Impl := sorry

/-- The second design. -/
def designB : Impl := sorry

/-- The input on which the two designs differ. -/
def input : Input := sorry

/-- The first design passes each law. -/
theorem a_passes : Passes designA := sorry

/-- The second design passes each law. -/
theorem b_passes : Passes designB := sorry

/-- The input is legal. -/
theorem input_legal : Legal input := sorry

/-- The two designs give different outputs on the input. -/
theorem differ : designA input ≠ designB input := sorry

end HPGap
"""


def complete_challenge(ns: str) -> str:
    return HEADER + f"""import Types
import Laws

open {ns}

namespace HPComplete

/-- Two designs that pass each law agree on each legal input. -/
theorem laws_complete : ∀ f g : Impl, Passes f → Passes g →
    ∀ x : Input, Legal x → f x = g x := sorry

end HPComplete
"""


def runner(ns: str) -> str:
    return HEADER + f"""-- Reads one encoded input on each line of stdin. Prints `encodeOutput (ref x)`
-- for each line, or `DECODE_ERROR` when the line does not decode.
import Types
import Ref
import Codec

open {ns}

partial def hpLoop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let raw ← stdin.getLine
  if raw.isEmpty then
    return
  let line := String.ofList (raw.toList.filter (fun c => c != '\\n' && c != '\\r'))
  match decodeInput line with
  | some x => stdout.putStrLn (encodeOutput (ref x))
  | none => stdout.putStrLn "DECODE_ERROR"
  hpLoop stdin stdout

def main : IO Unit := do
  hpLoop (← IO.getStdin) (← IO.getStdout)
"""


def question_gap(ns: str) -> str:
    return HEADER + f"""-- Prints the question of an accepted gap certificate, one `key<TAB>value` line each.
import Types
import Ref
import Codec
import GapSolution

open {ns}

def main : IO Unit := do
  let x := HPGap.input
  IO.println s!"input_encoded\\t{{encodeInput x}}"
  IO.println s!"input_shown\\t{{showInput x}}"
  IO.println s!"a_encoded\\t{{encodeOutput (HPGap.designA x)}}"
  IO.println s!"a_shown\\t{{showOutput (HPGap.designA x)}}"
  IO.println s!"b_encoded\\t{{encodeOutput (HPGap.designB x)}}"
  IO.println s!"b_shown\\t{{showOutput (HPGap.designB x)}}"
  IO.println s!"ref_encoded\\t{{encodeOutput (ref x)}}"
  IO.println s!"ref_shown\\t{{showOutput (ref x)}}"
"""


def question_conflict(ns: str) -> str:
    return HEADER + f"""-- Prints the question of an accepted conflict certificate, one `key<TAB>value` line each.
import Types
import Ref
import Codec
import ConflictSolution

open {ns}

def main : IO Unit := do
  let x := HPConflict.input
  IO.println s!"input_encoded\\t{{encodeInput x}}"
  IO.println s!"input_shown\\t{{showInput x}}"
  IO.println s!"ref_encoded\\t{{encodeOutput (ref x)}}"
  IO.println s!"ref_shown\\t{{showOutput (ref x)}}"
"""


def generated_texts(ns: str) -> dict:
    """The files that `generate` writes, as {name under hp/: text}."""
    return {
        "lakefile.toml": lakefile(),
        "lean-toolchain": TOOLCHAIN,
        "lake-manifest.json": manifest(),
        ".gitignore": ".lake/\n",
        "HPRefChallenge.lean": ref_challenge(ns),
        "HPGapChallenge.lean": gap_challenge(ns),
        "HPCompleteChallenge.lean": complete_challenge(ns),
        "comparator_ref.json": comparator_config("ref"),
        "comparator_gap.json": comparator_config("gap"),
        "comparator_complete.json": comparator_config("complete"),
        "Runner.lean": runner(ns),
        "QuestionGap.lean": question_gap(ns),
        "QuestionConflict.lean": question_conflict(ns),
    }


def write_if_changed(path: Path, text: str) -> bool:
    if path.exists() and path.read_text(encoding="utf-8") == text:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return True


def generate(domain: Domain) -> dict:
    ns = domain.config()["namespace"]
    written = []
    for name, text in generated_texts(ns).items():
        if write_if_changed(domain.gen / name, text):
            written.append(name)
    return {"dir": str(domain.gen), "files": sorted(generated_texts(ns)), "written": written}


def write_conflict(domain: Domain, law: str) -> None:
    ns = domain.config()["namespace"]
    write_if_changed(domain.gen / "HPConflictChallenge.lean", conflict_challenge(ns, law))
    write_if_changed(domain.gen / "comparator_conflict.json", comparator_config("conflict"))
