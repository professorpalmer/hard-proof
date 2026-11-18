"""hardproof link adapter for the domain `sync`. AUTHOR FILE (pinned).

Ported from `exp12/base/sync_link.py`. A case is a tuple
`(enable, locked, starter, registry)`: `enable` is 0 or 1, `locked` is a sorted
list of adapter numbers, and `starter` and `registry` are lists of rows
`(id, adapter, model, enabled)`.

One part of the real code is simulated: `starter_registry()` returns the
starter list of the case. The real `plan_starter_sync` reads the starter list
from that call. The append of `sync_starter_registry` is done here: the new
registry is the old registry followed by the additions.
"""
from __future__ import annotations

ADAPTERS = {1: "claude-code", 2: "cursor", 3: "codex"}
BACK = {name: number for number, name in ADAPTERS.items()}


def rows_text(rows) -> str:
    return ";".join(",".join(str(v) for v in row) for row in rows)


def rows_of(text: str) -> list:
    if not text:
        return []
    return [tuple(int(v) for v in row.split(",")) for row in text.split(";")]


def gen(rng):
    enable = rng.randint(0, 1)
    locked = sorted(a for a in ADAPTERS if rng.random() < 0.35)

    def row(i: int):
        return (i, rng.randint(1, 3), rng.randint(1, 4), rng.randint(0, 1))

    reg_ids = rng.sample(range(1, 13), rng.randint(0, 5))
    starter_ids = rng.sample(range(1, 13), rng.randint(0, 7))
    starter = [row(i) for i in starter_ids]
    if starter and rng.random() < 0.1:
        # A starter list with one id two times: not a legal input.
        starter = starter + [rng.choice(starter)]
        rng.shuffle(starter)
    return (enable, locked, starter, [row(i) for i in reg_ids])


def encode(case) -> str:
    enable, locked, starter, registry = case
    return f"{enable}|{','.join(str(a) for a in locked)}|{rows_text(starter)}|{rows_text(registry)}"


def decode(line: str):
    en, locked, starter, registry = line.split("|")
    return (int(en), [int(a) for a in locked.split(",")] if locked else [], rows_of(starter),
            rows_of(registry))


def call(func, case):
    enable, locked, starter, registry = case
    module = func.__globals__
    spec_type = module["ModelSpec"]

    def spec(row):
        i, a, m, e = row
        return spec_type(id=f"id-{i}", adapter=ADAPTERS[a], adapter_model_name=f"model-{m}",
                         enabled=bool(e))

    starter_specs = [spec(r) for r in starter]
    module["starter_registry"] = lambda: list(starter_specs)
    allowed = [name for number, name in ADAPTERS.items() if number not in locked]
    additions, _covered = func([spec(r) for r in registry], enabled_adapters=allowed, enable=bool(enable))
    added = [(int(a.spec.id.split("-")[1]), BACK[a.spec.adapter],
              int(a.spec.adapter_model_name.split("-")[1]), 1 if a.spec.enabled else 0)
             for a in additions]
    return list(registry) + added


def encode_result(result) -> str:
    return rows_text(result)


def is_legal(case) -> bool:
    ids = [row[0] for row in case[2]]
    return len(ids) == len(set(ids))
