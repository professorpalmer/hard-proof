"""The author stubs that `new` writes. Each stub holds short instructions."""
from __future__ import annotations

import json


def stubs(name: str, module: str, function: str, ns: str = "HP") -> dict:
    cfg = {"name": name, "namespace": ns, "python": {"module": module, "function": function},
           "banned_in_laws": ["ref"]}
    return {
        "hardproof.json": json.dumps(cfg, indent=2) + "\n",
        "Types.lean": f"""/-
AUTHOR FILE. Write the types of `{module}.{function}` here.

- `Input` and `Output`, each with `deriving DecidableEq`.
- `abbrev Impl := Input → Output`.
- `def legal : Input → Bool` and `def Legal (x : Input) : Prop := legal x = true`.
- The words that a law can use.
Do not write `ref` here. Do not import other files of this folder.
-/

namespace {ns}

-- structure Input where
--   ...
-- deriving DecidableEq, Repr

end {ns}
""",
        "Ref.lean": f"""/-
AUTHOR FILE. Write `def {ns}.ref : {ns}.Impl` here: the mirror of the Python code.
Put its helper functions here too. No `sorry`, no `axiom`, no `native_decide`.
-/
import Types

namespace {ns}

-- def ref : Impl := fun x => ...

end {ns}
""",
        "Codec.lean": f"""/-
AUTHOR FILE. One line of text for each value.

- `decodeInput : String → Option Input`
- `encodeInput : Input → String` (the same format as `encode` in link_adapter.py)
- `encodeOutput : Output → String` (the same format as `encode_result`)
- `showInput : Input → String` and `showOutput : Output → String` (for the human)
-/
import Types

namespace {ns}

end {ns}
""",
        "link_adapter.py": f'''"""AUTHOR FILE. The link adapter for `{module}.{function}`.

Write these six functions. A case is any Python value that `==` compares.
"""
from __future__ import annotations


def gen(rng):
    """Return one random case. `rng` is a `random.Random`."""
    raise NotImplementedError


def encode(case) -> str:
    """Return the case as one line, in the format of `encodeInput`."""
    raise NotImplementedError


def decode(line: str):
    """Return the case of a line. `decode(encode(c)) == c` must hold."""
    raise NotImplementedError


def call(func, case):
    """Call the real function (or a mutant of it) on the case."""
    raise NotImplementedError


def encode_result(result) -> str:
    """Return the result as one line, in the format of `encodeOutput`."""
    raise NotImplementedError


def is_legal(case) -> bool:
    """Return True when the case is legal (the same rule as `legal`)."""
    raise NotImplementedError
''',
        "DESCRIPTION.md": f"""# {name}: the documentation sentences

Write each sentence of the documentation of `{module}.{function}` as an exact
quote, with its source file.

1. "..." (source: `path/to/file.py`)

## Model words and documentation words

| Model word | Documentation word |
| --- | --- |
""",
        "Laws.lean": f"""/-
AUTHOR FILE. The laws. Import `Types` only. Do not name `ref`.

- One `def <Name> (f : Impl) : Prop` for each law.
- `def Passes (f : Impl) : Prop` is the conjunction of all laws.
- `theorem some_design_fails : ∃ f : Impl, ¬ Passes f`.
-/
import Types

namespace {ns}

end {ns}
""",
    }
