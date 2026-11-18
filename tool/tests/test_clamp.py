"""The small example `examples/clamp`: a domain with no outside repository."""
from __future__ import annotations

import json
import unittest

from helpers import DomainCase


class ClampTest(DomainCase):
    example = "clamp"

    def test_model_laws_ref(self):
        code, report = self.hp("check", "model", "laws", "ref")
        self.assertAccept(code, report)
        for kind in ("model", "laws", "ref"):
            self.assertEqual(self.result(report, kind)["verdict"], "accept", kind)
        self.assertEqual(self.result(report, "laws")["laws"],
                         ["InRange", "BelowGivesLo", "AboveGivesHi", "InsideGivesX"])
        self.assertEqual(self.result(report, "model")["round_trip_cases"], 200)

    def test_ref_paranoid(self):
        code, report = self.hp("check", "ref", "--paranoid")
        self.assertAccept(code, report)
        self.assertIn("--paranoid", self.result(report, "ref")["comparator_flags"])

    def test_model_rejects_a_codec_mismatch(self):
        self.write("Codec.lean", self.read("Codec.lean").replace('(s.splitOn ",")', '(s.splitOn ";")'))
        code, report = self.hp("check", "model")
        self.assertReject(code, report)
        res = self.result(report, "model")
        self.assertEqual(res["stage"], "codec")
        self.assertIn("cannot decode", res["problems"][0])

    def test_model_rejects_a_hole_in_ref(self):
        self.write("Ref.lean", "import Types\nnamespace HP\ndef ref : Impl := fun _ => sorry\nend HP\n")
        code, report = self.hp("check", "model")
        self.assertReject(code, report)
        self.assertEqual(self.result(report, "model")["stage"], "text")

    def test_link_with_mutants(self):
        code, report = self.hp("link", "--repo", str(self.dir / "pycode"), "--cases", "3000", "--mutants", "40")
        self.assertEqual(report["verdict"], "agree", json.dumps(report, indent=1))
        self.assertEqual(code, 0)
        self.assertEqual(report["cases"], 3000)
        self.assertEqual(report["differences"], 0)
        mut = report["mutants"]
        self.assertTrue(mut["identity_copy_agrees"])
        self.assertGreaterEqual(mut["killed"], 1)
        self.assertEqual(mut["made"], mut["killed"] + len(mut["survived"]))

    def test_link_finds_a_wrong_function(self):
        wrong = self.dir / "wrong.py"
        wrong.write_text("def clamp(x, lo, hi):\n    return max(lo, min(x, hi - 1))\n", encoding="utf-8")
        code, report = self.hp("link", "--repo", str(self.dir), "--function-file", str(wrong),
                               "--cases", "500", "--mutants", "0")
        self.assertEqual(report["verdict"], "disagree")
        self.assertEqual(code, 1)
        self.assertGreater(report["differences"], 0)
        self.assertIsNotNone(report["first_difference"])

    def test_run_log_and_status(self):
        self.hp("check", "laws")
        lines = [json.loads(l) for l in self.read("hardproof_runs.jsonl").splitlines()]
        self.assertEqual(len(lines), 1)
        for key in ("time", "actor", "command", "verdict", "seconds"):
            self.assertIn(key, lines[0])
        self.assertEqual(lines[0]["actor"], "test")
        code, report = self.hp("status")
        self.assertEqual(code, 0)
        self.assertEqual(report["last_check"]["laws"]["verdict"], "accept")
        self.assertTrue(report["author_files"]["Laws.lean"])
        self.assertTrue(report["solution_files"]["ref"])
        self.assertFalse(report["solution_files"]["gap"])

    def test_question_needs_a_certificate(self):
        code, report = self.hp("question")
        self.assertEqual(report["verdict"], "reject")
        self.assertEqual(code, 1)

    def test_usage_error(self):
        code, report = self.hp("check", "nonsense")
        self.assertEqual(code, 2)
        self.assertEqual(report["verdict"], "usage_error")

    def test_new_and_generate(self):
        target = self.dir.parent / "fresh"
        code, report = self.hp("new", str(target), "--name", "f", "--module", "pkg.mod", "--function", "f")
        self.assertEqual(code, 0, report)
        for name in ("hardproof.json", "Types.lean", "Ref.lean", "Codec.lean", "link_adapter.py",
                     "DESCRIPTION.md", "Laws.lean", "hp/lakefile.toml", "hp/lake-manifest.json",
                     "hp/HPGapChallenge.lean", "hp/Runner.lean"):
            self.assertTrue((target / name).exists(), name)
        (target / "hp" / "HPGapChallenge.lean").write_text("edited\n", encoding="utf-8")
        code, report = self.hp("generate")
        self.assertEqual(code, 0)
        from helpers import run_hp
        code, report = run_hp(target, "generate")
        self.assertIn("HPGapChallenge.lean", report["written"])


if __name__ == "__main__":
    unittest.main()
