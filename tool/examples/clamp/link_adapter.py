"""hardproof link adapter for the domain `clamp`. AUTHOR FILE (pinned).

A case is a tuple `(x, lo, hi)` of integers. The line format is `x,lo,hi`,
the same as `HP.encodeInput` in `Codec.lean`.
"""
from __future__ import annotations


def gen(rng):
    lo = rng.randint(-20, 20)
    hi = lo + rng.randint(-3, 25)
    return (rng.randint(-40, 40), lo, hi)


def encode(case) -> str:
    return ",".join(str(v) for v in case)


def decode(line: str):
    return tuple(int(v) for v in line.split(","))


def call(func, case):
    x, lo, hi = case
    return func(x, lo, hi)


def encode_result(result) -> str:
    return str(result)


def is_legal(case) -> bool:
    return case[1] <= case[2]
