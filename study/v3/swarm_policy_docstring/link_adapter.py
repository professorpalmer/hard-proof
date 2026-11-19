"""hardproof link adapter for the domain `swarm_policy`. AUTHOR FILE (pinned).

A case is a tuple of four booleans: refusal, launch, narrow, broad.
The line format is four digits, the same as `HP.encodeInput` in `Codec.lean`.
"""
from __future__ import annotations


def gen(rng):
    return tuple(rng.random() < 0.5 for _ in range(4))


def encode(case) -> str:
    return "".join("1" if v else "0" for v in case)


def decode(line: str):
    return tuple(c == "1" for c in line.strip())


def call(func, case):
    return func(*case)


def encode_result(result) -> str:
    return str(result)


def is_legal(case) -> bool:
    return True
