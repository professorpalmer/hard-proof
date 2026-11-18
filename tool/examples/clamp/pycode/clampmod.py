"""A very small function under test for the hardproof example domain."""
from __future__ import annotations


def clamp(x: int, lo: int, hi: int) -> int:
    """Return x limited to the closed range from lo to hi.

    When x is less than lo, the result is lo. When x is more than hi, the
    result is hi. Else the result is x. The caller must give lo <= hi.
    """
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x
