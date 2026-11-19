"""The proof gate (command `hp`): one proof gate for one Python function.

A domain folder holds a Lean model of the function, its laws and the link
adapter. The tool generates the Lean project files and the challenge files,
and runs the checks. Each command prints one JSON report.
"""
from __future__ import annotations

from hpflow import __version__  # noqa: F401
