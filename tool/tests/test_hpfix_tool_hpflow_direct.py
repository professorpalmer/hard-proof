"""Regression tests of the runner: used-up retry edges, verdict edges of a failed run, and event lines."""
from __future__ import annotations

import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow.adapters import COMMAND  # noqa: E402
from hpflow.direct import DirectRunner, edge_matches, json_lines, read_claude  # noqa: E402

REVIEW_EDGES = [{"from": "review", "to": "done", "when": "PASS"},
                {"from": "review", "to": "build", "when": "FAIL", "max": 2},
                {"from": "review", "to": "build", "when": "PARTIAL", "max": 1},
                {"from": "review", "to": "done", "when": "PARTIAL"}]
CHECK_EDGES = [{"from": "check", "to": "done", "when": "ok"},
               {"from": "check", "to": "work", "when": "fail", "max": 1},
               {"from": "check", "to": "failed", "when": "fail"}]


def step(graph, node, ok, verdict, counts):
    return DirectRunner._next(graph, node, {"ok": ok, "verdict": verdict}, counts)


class UsedUpEdge(unittest.TestCase):
    def test_partial_twice_reaches_done(self):
        graph, node, counts = {"edges": REVIEW_EDGES}, {"id": "review", "kind": "judge"}, {}
        self.assertEqual(step(graph, node, True, "PARTIAL", counts), "build")
        self.assertEqual(step(graph, node, True, "PARTIAL", counts), "done")

    def test_fail_beyond_max_without_fallback_stays_stuck(self):
        graph, node, counts = {"edges": REVIEW_EDGES}, {"id": "review", "kind": "judge"}, {}
        self.assertEqual(step(graph, node, True, "FAIL", counts), "build")
        self.assertEqual(step(graph, node, True, "FAIL", counts), "build")
        self.assertEqual(step(graph, node, True, "FAIL", counts), "stuck")

    def test_check_fails_twice_ends_failed(self):
        graph, node, counts = {"edges": CHECK_EDGES}, {"id": "check", "kind": "shell"}, {}
        self.assertEqual(step(graph, node, False, None, counts), "work")
        self.assertEqual(step(graph, node, False, None, counts), "failed")

    def test_check_ok_after_repair_still_done(self):
        graph, node, counts = {"edges": CHECK_EDGES}, {"id": "check", "kind": "shell"}, {}
        self.assertEqual(step(graph, node, False, None, counts), "work")
        self.assertEqual(step(graph, node, True, None, counts), "done")

    @unittest.skipUnless(shutil.which("cat"), "needs cat")
    def test_run_of_a_failing_check_ends_failed(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            graph = {"id": "g1", "entry": "work",
                     "defaults": {"adapter": COMMAND, "model": "m", "timeout_seconds": 30},
                     "nodes": [{"id": "work", "kind": "agent", "task": "t", "payload": {"command": "cat {prompt_file}"}},
                               {"id": "check", "kind": "shell", "command": "exit 1"},
                               {"id": "done", "kind": "end", "status": "pass"},
                               {"id": "failed", "kind": "end", "status": "fail"}],
                     "edges": [{"from": "work", "to": "check", "when": "ok"}, *CHECK_EDGES,
                               {"from": "work", "to": "failed"}]}
            r = DirectRunner(d / "graphs").run(graph, d / "work")
            self.assertEqual(r["status"], "failed")
            self.assertEqual([s["node"] for s in r["steps"]], ["work", "check", "work", "check"])


class VerdictOfFailedRun(unittest.TestCase):
    def test_failed_run_does_not_follow_pass(self):
        self.assertFalse(edge_matches("PASS", False, "PASS"))

    def test_failed_judge_ends_failed_not_done(self):
        graph, node = {"edges": REVIEW_EDGES}, {"id": "review", "kind": "judge"}
        self.assertEqual(step(graph, node, False, "PASS", {}), "failed")

    def test_ok_run_follows_its_verdict(self):
        self.assertTrue(edge_matches("PASS", True, "PASS"))
        self.assertFalse(edge_matches("FAIL", True, "PASS"))
        self.assertTrue(edge_matches("fail", False, "PASS"))


class EventLines(unittest.TestCase):
    def test_raw_line_separators_stay_in_the_event(self):
        for ch in (" ", " ", "\x85", "\x0b", "\x0c", "\x1c"):
            line = json.dumps({"type": "result", "result": f"a{ch}b"}, ensure_ascii=False)
            self.assertEqual(json_lines(line + "\n"), [{"type": "result", "result": f"a{ch}b"}])

    def test_result_with_separator_is_done(self):
        out = json.dumps({"type": "result", "result": "x VERDICT: PASS - ok", "session_id": "s",
                          "total_cost_usd": 0.5}, ensure_ascii=False)
        got = read_claude(out + "\n")
        self.assertTrue(got["done"])
        self.assertEqual(got["session"], "s")

    def test_crlf_and_noise_lines_keep_their_result(self):
        text = 'noise\r\n{"a": 1}\r\n{bad\n\n[1]\n{"b": 2}'
        self.assertEqual(json_lines(text), [{"a": 1}, {"b": 2}])


if __name__ == "__main__":
    unittest.main()
