"""The checks: model, laws, and the four certificate kinds."""
from __future__ import annotations

import importlib.util
import random
import re
import sys
from pathlib import Path

from hpflow.proof import lean
from hpflow.proof.domain import Domain, DomainError, IDENT
from hpflow.proof.generate import KINDS, generate, write_conflict

MODEL_FILES = ["Types.lean", "Ref.lean", "Codec.lean"]
LOCAL_MODULES = {"Types", "Ref", "Codec", "Laws", "RefPassesSolution", "ConflictSolution",
                 "GapSolution", "CompleteSolution"}
ROUND_TRIP_CASES = 200


def result(kind: str) -> dict:
    return {"kind": kind, "verdict": "reject", "stage": "", "problems": []}


def reject(res: dict, stage: str, problems: list, output: str = None) -> dict:
    res.update(stage=stage, problems=problems)
    if output:
        res["output"] = output
    return res


def load_adapter(domain: Domain):
    path = domain.path("link_adapter.py")
    if not path.exists():
        raise DomainError("link_adapter.py does not exist")
    name = f"hardproof_link_adapter_{abs(hash(str(path)))}"
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    missing = [f for f in ("gen", "encode", "decode", "call", "encode_result", "is_legal")
               if not callable(getattr(module, f, None))]
    if missing:
        raise DomainError("link_adapter.py does not define: " + ", ".join(missing))
    return module


def run_runner(domain: Domain, lines: list) -> tuple:
    """Send encoded inputs to `Runner.lean`. Return (outputs or None, error text)."""
    text = "".join(l + "\n" for l in lines)
    rc, out, err = lean.run(["lake", "env", "lean", "--run", "Runner.lean"], domain.gen, stdin=text)
    if rc != 0:
        return None, lean.clean(out + err)
    got = out.split("\n")
    if len(got) < len(lines):
        return None, f"the runner printed {len(got)} lines for {len(lines)} inputs"
    return got[: len(lines)], ""


# ---------------------------------------------------------------- model

def check_model(domain: Domain) -> dict:
    res = result("model")
    ns = domain.config()["namespace"]
    absent = [f for f in MODEL_FILES + ["link_adapter.py"] if not domain.path(f).exists()]
    if absent:
        return reject(res, "absent_file", [f"{f} does not exist" for f in absent])
    problems = []
    for name in MODEL_FILES:
        code = lean.strip_comments(domain.path(name).read_text(encoding="utf-8"))
        problems += [f"{name}: {p}" for p in lean.forbidden(code)]
        local = [m for m in lean.imports(code) if m in LOCAL_MODULES]
        allowed = {"Types.lean": set(), "Ref.lean": {"Types"}, "Codec.lean": {"Types"}}[name]
        bad = [m for m in local if m not in allowed]
        if bad:
            problems.append(f"{name}: imports {', '.join(bad)} (allowed: {sorted(allowed) or 'none'})")
    types_code = lean.strip_comments(domain.path("Types.lean").read_text(encoding="utf-8"))
    if lean.word(types_code, "ref"):
        problems.append("Types.lean: names `ref` (the mirror of the code belongs in Ref.lean)")
    if problems:
        return reject(res, "text", problems)
    generate(domain)
    ok, out = lean.build(domain.gen, "HPModel")
    if not ok:
        return reject(res, "build", ["Types, Ref or Codec does not build"], out)
    probe_lines = [
        "import Types", "import Ref", "import Codec",
        f"example : Type := {ns}.Input",
        f"example : Type := {ns}.Output",
        f"example : DecidableEq {ns}.Input := inferInstance",
        f"example : DecidableEq {ns}.Output := inferInstance",
        f"example : {ns}.Impl = ({ns}.Input → {ns}.Output) := rfl",
        f"example : {ns}.Input → Bool := {ns}.legal",
        f"example : ∀ x : {ns}.Input, {ns}.Legal x = ({ns}.legal x = true) := fun _ => rfl",
        f"example : {ns}.Impl := {ns}.ref",
        f"example : String → Option {ns}.Input := {ns}.decodeInput",
        f"example : {ns}.Input → String := {ns}.encodeInput",
        f"example : {ns}.Output → String := {ns}.encodeOutput",
        f"example : {ns}.Input → String := {ns}.showInput",
        f"example : {ns}.Output → String := {ns}.showOutput",
        f"#print axioms {ns}.ref",
    ]
    rc, out = lean.probe(domain.gen, "model_check", "\n".join(probe_lines) + "\n")
    errs = lean.error_lines(out, "model_check")
    if rc != 0 or errs:
        bad = [f"`{probe_lines[n - 1]}` fails: {'; '.join(m)}" for n, m in sorted(errs.items())]
        return reject(res, "statement", bad or ["the model probe does not elaborate"], lean.clean(out))
    used = set(lean.axioms(out).get(f"{ns}.ref", []))
    if used - lean.PERMITTED:
        return reject(res, "axioms", [f"ref uses axiom {a}" for a in sorted(used - lean.PERMITTED)])
    rc, out, err = lean.run(["lake", "env", "lean", "Runner.lean"], domain.gen)
    if rc != 0:
        return reject(res, "runner", ["Runner.lean does not build"], lean.clean(out + err))
    adapter = load_adapter(domain)
    rng = random.Random(0)
    cases = [adapter.gen(rng) for _ in range(ROUND_TRIP_CASES)]
    lines = []
    for case in cases:
        line = adapter.encode(case)
        if "\n" in line or "\r" in line:
            return reject(res, "codec", [f"encode gives more than one line for {case!r}"])
        back = adapter.decode(line)
        if back != case:
            return reject(res, "codec", [f"decode(encode(c)) != c for c = {case!r} (line {line!r})"])
        lines.append(line)
    got, error = run_runner(domain, lines)
    if got is None:
        return reject(res, "runner", ["Runner.lean failed on the round trip cases"], error)
    bad = [lines[i] for i, g in enumerate(got) if g == "DECODE_ERROR"]
    if bad:
        return reject(res, "codec", [f"the Lean runner cannot decode {len(bad)} of {len(lines)} lines",
                                     f"first line: {bad[0]!r}"])
    legal = sum(1 for c in cases if adapter.is_legal(c))
    res.update(verdict="accept", stage="done", round_trip_cases=len(cases), legal_cases=legal)
    return res


# ---------------------------------------------------------------- laws

def law_names(domain: Domain) -> list:
    path = domain.path("Laws.lean")
    if not path.exists():
        return []
    code = lean.strip_comments(path.read_text(encoding="utf-8"))
    names = re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?def\s+([A-Za-z_][A-Za-z0-9_']*)\s*\(\s*f\s*:\s*Impl\s*\)\s*:\s*Prop",
                       code, flags=re.M)
    return [n for n in names if n != "Passes"]


def check_laws(domain: Domain) -> dict:
    res = result("laws")
    cfg = domain.config()
    ns = cfg["namespace"]
    path = domain.path("Laws.lean")
    if not path.exists():
        return reject(res, "absent_file", ["Laws.lean does not exist"])
    code = lean.strip_comments(path.read_text(encoding="utf-8"))
    problems = []
    imported = lean.imports(code)
    if imported != ["Types"]:
        problems.append(f"Laws.lean must import `Types` only; it imports {imported}")
    m = re.search(r"theorem\s+some_design_fails\b", code)
    if not m:
        problems.append("Laws.lean does not declare `theorem some_design_fails`")
    before = code[: m.start()] if m else code
    for banned in cfg["banned_in_laws"]:
        if lean.word(before, banned):
            problems.append(f"a law names `{banned}` (a banned word before `theorem some_design_fails`)")
    problems += lean.forbidden(code)
    if problems:
        return reject(res, "text", problems)
    generate(domain)
    ok, out = lean.build(domain.gen, "HPLaws")
    if not ok:
        return reject(res, "build", ["Laws.lean does not build"], out)
    laws = law_names(domain)
    probe_lines = [
        "import Laws",
        f"example : {ns}.Impl → Prop := {ns}.Passes",
        f"theorem HardProofGate.some_design_fails : ∃ f : {ns}.Impl, ¬ {ns}.Passes f := {ns}.some_design_fails",
    ]
    probe_lines += [f"example : {ns}.Impl → Prop := {ns}.{law}" for law in laws]
    probe_lines += ["#print axioms HardProofGate.some_design_fails", f"#print axioms {ns}.Passes"]
    rc, out = lean.probe(domain.gen, "laws_check", "\n".join(probe_lines) + "\n")
    errs = lean.error_lines(out, "laws_check")
    if rc != 0 or errs:
        bad = [f"`{probe_lines[n - 1]}` fails: {'; '.join(msg)}" for n, msg in sorted(errs.items())]
        return reject(res, "statement", bad or ["the declarations have a different statement"], lean.clean(out))
    used = set()
    for names in lean.axioms(out).values():
        used |= set(names)
    bad = sorted(used - lean.PERMITTED)
    if bad:
        return reject(res, "axioms", [f"axiom not permitted: {a}" for a in bad])
    res.update(verdict="accept", stage="done", laws=laws)
    return res


# ---------------------------------------------------------------- certificates

def conflict_law(domain: Domain) -> tuple:
    """Read the `-- hardproof-law: <Law>` line. Return (law or None, problem)."""
    text = domain.path("ConflictSolution.lean").read_text(encoding="utf-8")
    first = next((l for l in text.splitlines() if l.strip()), "")
    m = re.match(r"^--\s*hardproof-law:\s*(\S+)\s*$", first)
    if not m:
        return None, "ConflictSolution.lean must start with the line `-- hardproof-law: <Law>`"
    law = m.group(1)
    if not IDENT.match(law):
        return None, f"`{law}` is not a law name"
    laws = law_names(domain)
    if law not in laws:
        return None, f"`{law}` is not a law of Laws.lean (laws: {', '.join(laws)})"
    return law, ""


def check_certificate(domain: Domain, kind: str, paranoid: bool) -> dict:
    res = result(kind)
    solution, _challenge, config, theorems, defs = KINDS[kind]
    if not domain.path(f"{solution}.lean").exists():
        return reject(res, "absent_file", [f"{solution}.lean does not exist"])
    generate(domain)
    if kind == "conflict":
        law, problem = conflict_law(domain)
        if law is None:
            return reject(res, "law", [problem])
        res["law"] = law
        write_conflict(domain, law)
    ok, out = lean.build(domain.gen, f"HP{kind.capitalize()}Work")
    if not ok:
        return reject(res, "build", [f"{solution}.lean does not build"], out)
    names = theorems + defs
    text = f"import {solution}\n" + "".join(f"#check @{n}\n" for n in names)
    _rc, out = lean.probe(domain.gen, f"{kind}_names", text)
    errs = lean.error_lines(out, f"{kind}_names")
    absent = [names[n - 2] for n in sorted(errs) if 2 <= n < 2 + len(names)]
    if absent or 1 in errs:
        return reject(res, "absent_name", [f"{solution}.lean does not declare {n}" for n in absent]
                      or ["the name probe failed"], lean.clean(out))
    ok, out = lean.build(domain.gen, f"HP{kind.capitalize()}Challenge")
    if not ok:
        return reject(res, "challenge", ["the generated challenge does not build (check the laws)"], out)
    rc, out, flags = lean.comparator(domain.gen, config, paranoid)
    res["comparator_flags"] = flags
    if paranoid:
        res["kernels"] = kernel_report(out)
    if rc != 0 and paranoid and res["kernels"]["crashed"] and not res["kernels"]["rejected"]:
        # An extra kernel that crashes (a stack overflow on a deep proof term) gives no verdict about the proof.
        # The statement match, the axiom audit and the default kernel must then pass in a run of their own.
        rc2, out2, _flags = lean.comparator(domain.gen, config, False)
        if rc2 == 0:
            res.update(verdict="accept", stage="done",
                       note="accepted by " + ", ".join(res["kernels"]["accepted"]) + "; no verdict from "
                            + ", ".join(res["kernels"]["crashed"]) + " (the kernel process crashed)")
            return res
        rc, out = rc2, out2
    if rc in (124, 137) and ("memory limit" in out or "timeout" in out):
        return reject(res, "resource_limit", ["the check stopped at a resource limit, so it gives no verdict: " + out[-200:]], out)
    if rc != 0:
        reason = "the comparator rejects the solution"
        if "does not match" in out or "mismatch" in out.lower():
            reason += " (a statement does not match)"
        elif "axiom" in out.lower():
            reason += " (an axiom that is not permitted)"
        return reject(res, "comparator", [f"{reason}; exit code {rc}"], out)
    res.update(verdict="accept", stage="done")
    return res


def kernel_report(out: str) -> dict:
    """Which kernels of a `--paranoid` comparator run accept, reject, or crash."""
    accepted, rejected, crashed = [], [], []
    for name, word in re.findall(r"^(.+?) kernel (accepts|rejected) the solution", out, flags=re.M):
        name = name.strip()
        (accepted if word == "accepts" else rejected).append(name)
    for name in re.findall(r"error: (\S+) exited with (?:134|139|-6|-11)", out):
        crashed.append(name)
    if "has overflowed its stack" in out and not crashed:
        crashed.append("unknown kernel")
    rejected = [n for n in rejected if n not in crashed]
    return {"accepted": accepted, "rejected": rejected, "crashed": crashed}


def check(domain: Domain, kind: str, paranoid: bool) -> dict:
    if kind == "model":
        return check_model(domain)
    if kind == "laws":
        return check_laws(domain)
    return check_certificate(domain, kind, paranoid)
