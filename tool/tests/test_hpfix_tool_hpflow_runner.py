"""Regression tests of the repair edge of `agent_graph` as the direct runner walks it."""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow import adapters  # noqa: E402
from hpflow.commands import fix_graph  # noqa: E402
from hpflow.direct import DirectRunner  # noqa: E402
from hpflow.runner import agent_graph  # noqa: E402


def walk(repairs, items):
    g = agent_graph("f", "t", ["a"], "claude-code", "m", {}, check="false", repairs=repairs)
    node = next(n for n in g["nodes"] if n["id"] == "check")
    counts = {}
    return [DirectRunner._next(g, node, dict(item), counts) for item in items]


FAIL = {"ok": False, "verdict": None}
OK = {"ok": True, "verdict": None}


class RepairEdge(unittest.TestCase):
    def test_a_check_that_still_fails_after_the_repair_ends_failed(self):
        self.assertEqual(walk(1, [FAIL, FAIL]), ["work", "failed"])

    def test_a_check_that_fails_with_no_repairs_ends_failed(self):
        self.assertEqual(walk(0, [FAIL]), ["failed"])

    def test_a_check_that_passes_after_the_repair_ends_done(self):
        self.assertEqual(walk(1, [FAIL, OK]), ["work", "done"])

    def test_an_exhausted_edge_with_no_fallback_is_still_stuck(self):
        g = {"edges": [{"from": "check", "to": "work", "when": "fail", "max": 1}]}
        node = {"id": "check", "kind": "shell"}
        counts = {}
        self.assertEqual([DirectRunner._next(g, node, dict(FAIL), counts) for _ in range(2)], ["work", "stuck"])


class FixGraphEdges(unittest.TestCase):
    """The graph of `hpf fix` has the same fallback edges after its edges with a max."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        tmp = Path(self._tmp.name)
        ctx = SimpleNamespace(lean=False, effort=adapters.DEFAULT_EFFORT, src=tmp)
        audit = {"python": "python", "test_cmd": "{python} -m pytest {tests}", "repo": str(tmp), "paths": ["src"]}
        g = {"bugs": [], "slug": "s", "file": "src/a.py", "test_file": "tests/test_a.py"}
        self.graph = fix_graph(ctx, audit, g, "base", tmp / "info", adapters.DEFAULT_ADAPTER, None, "m", "j", "rules")
        self.nodes = {n["id"]: n for n in self.graph["nodes"]}

    def tearDown(self):
        self._tmp.cleanup()

    def walk(self, node, items):
        counts = {}
        return [DirectRunner._next(self.graph, self.nodes[node], dict(item), counts) for item in items]

    def test_a_check_that_fails_after_two_repairs_ends_failed(self):
        self.assertEqual(self.walk("check", [FAIL] * 3), ["build", "build", "failed"])

    def test_a_review_that_fails_after_two_repairs_ends_failed(self):
        self.assertEqual(self.walk("review", [{"ok": True, "verdict": "FAIL"}] * 3), ["build", "build", "failed"])

    def test_a_partial_review_after_one_repair_ends_done(self):
        self.assertEqual(self.walk("review", [{"ok": True, "verdict": "PARTIAL"}] * 2), ["build", "done"])

    def test_a_passing_review_ends_done(self):
        self.assertEqual(self.walk("review", [{"ok": True, "verdict": "PASS"}]), ["done"])


if __name__ == "__main__":
    unittest.main()
