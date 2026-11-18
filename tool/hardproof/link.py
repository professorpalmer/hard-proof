"""The link test: the Lean `ref` against the real Python function, then mutants."""
from __future__ import annotations

import importlib
import importlib.util
import random
import signal
import subprocess
import sys
import time
from pathlib import Path

from hardproof import mutate
from hardproof.checks import load_adapter, run_runner
from hardproof.domain import Domain, DomainError
from hardproof.generate import generate
from hardproof import lean

MUTANT_SECONDS = 30


class MutantTimeout(Exception):
    pass


def load_function(cfg: dict, repo: Path, function_file: Path = None):
    py = cfg["python"]
    if function_file is not None:
        spec = importlib.util.spec_from_file_location(f"hardproof_function_{abs(hash(str(function_file)))}",
                                                      function_file)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
    else:
        sys.path.insert(0, str(repo))
        module = importlib.import_module(py["module"])
    func = getattr(module, py["function"], None)
    if not callable(func):
        raise DomainError(f"{py['module']} has no function {py['function']}")
    return module, func


def outputs(adapter, func, cases: list, expected: list = None) -> tuple:
    """Run `func` on each case. Stop at the first difference when `expected` is given.

    Return (encoded results, index of the first difference or None, error text).
    """
    got = []
    for i, case in enumerate(cases):
        try:
            line = adapter.encode_result(adapter.call(func, case))
        except MutantTimeout:
            raise
        except Exception as exc:  # the function under test (or a mutant) can raise anything
            return got, i, f"{type(exc).__name__}: {exc}"
        got.append(line)
        if expected is not None and line != expected[i]:
            return got, i, ""
    return got, None, ""


def run_mutant(adapter, func, cases: list, expected: list) -> tuple:
    """Return (killed, how) for one mutant."""
    use_alarm = hasattr(signal, "SIGALRM")

    def on_alarm(_sig, _frame):
        raise MutantTimeout()

    if use_alarm:
        old = signal.signal(signal.SIGALRM, on_alarm)
        signal.alarm(MUTANT_SECONDS)
    try:
        _got, first, error = outputs(adapter, func, cases, expected)
    except MutantTimeout:
        return True, f"timeout after {MUTANT_SECONDS} seconds"
    finally:
        if use_alarm:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old)
    if first is None:
        return False, ""
    if error:
        return True, f"raises on case {first}: {error[:200]}"
    return True, f"differs on case {first}"


def link(domain: Domain, repo: Path, n_cases: int, seed: int, n_mutants: int,
         function_file: Path = None) -> dict:
    started = time.time()
    cfg = domain.config()
    report = {"command": "link", "verdict": "disagree",
              "function": f"{cfg['python']['module']}.{cfg['python']['function']}",
              "repo": str(repo), "seed": seed}
    generate(domain)
    ok, out = lean.build(domain.gen, "HPModel")
    if not ok:
        report.update(problems=["Types, Ref or Codec does not build"], output=out)
        return report
    adapter = load_adapter(domain)
    _module, func = load_function(cfg, repo, function_file)
    commit = ""
    if function_file is None and (repo / ".git").exists():
        commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=str(repo),
                                capture_output=True, text=True).stdout.strip()
    report["commit"] = commit or None
    rng = random.Random(seed)
    cases = []
    generated = 0
    while len(cases) < n_cases and generated < n_cases * 20:
        case = adapter.gen(rng)
        generated += 1
        if adapter.is_legal(case):
            cases.append(case)
    report["generated"] = generated
    report["illegal_skipped"] = generated - len(cases)
    lines = [adapter.encode(c) for c in cases]
    model, error = run_runner(domain, lines)
    if model is None:
        report.update(problems=["the Lean runner failed"], output=error)
        return report
    decode_errors = sum(1 for m in model if m == "DECODE_ERROR")
    code, first_bad, err = outputs(adapter, func, cases)
    if first_bad is not None:
        report.update(problems=[f"the real function raises on case {first_bad}: {err}"],
                      first_difference={"input": lines[first_bad], "error": err})
        return report
    differ = [i for i in range(len(cases)) if code[i] != model[i]]
    first = None
    if differ:
        i = differ[0]
        first = {"input": lines[i], "lean_ref": model[i], "python": code[i]}
    report.update(cases=len(cases), decode_errors=decode_errors, differences=len(differ),
                  first_difference=first)

    mut = {"requested": n_mutants}
    try:
        identity, made, total_sites = mutate.mutants(func, n_mutants, seed)
    except (OSError, TypeError, ValueError) as exc:
        mut.update(error=f"the mutator cannot read the function: {exc}", made=0, killed=0)
        report["mutants"] = mut
    else:
        killed_id, how = run_mutant(adapter, identity, cases, model)
        mut["identity_copy_agrees"] = not killed_id
        if killed_id:
            mut["identity_copy_problem"] = how
        killed = 0
        survivors = []
        broken = []
        for desc, fn in made:
            if isinstance(fn, Exception):
                broken.append({"mutant": desc, "error": str(fn)})
                continue
            dead, _how = run_mutant(adapter, fn, cases, model)
            if dead:
                killed += 1
            else:
                survivors.append(desc)
        made_count = len(made) - len(broken)
        mut.update(sites=total_sites, made=made_count, killed=killed, survived=survivors,
                   kill_rate=round(killed / made_count, 3) if made_count else None)
        if broken:
            mut["not_compiled"] = broken
        report["mutants"] = mut
    ok = not differ and decode_errors == 0
    report["verdict"] = "agree" if ok else "disagree"
    report["seconds"] = round(time.time() - started, 2)
    return report
