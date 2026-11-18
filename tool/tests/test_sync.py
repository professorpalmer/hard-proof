"""The example `examples/sync`: the sync command of experiment 12 in the domain contract."""
from __future__ import annotations

import json
import unittest

from helpers import PUPPETMASTER, DomainCase

LAWS = ["KeepsRows", "AddsOnlyAbsent", "AddsAllAbsent", "NoSameIdentity", "DisabledByDefault",
        "LockedDisabled", "EnableKeepsState"]


class SyncTest(DomainCase):
    example = "sync"

    def test_model(self):
        code, report = self.hp("check", "model")
        self.assertAccept(code, report)

    @unittest.skipUnless((PUPPETMASTER / "puppetmaster" / "registry_sync.py").exists(),
                         f"the Puppetmaster clone {PUPPETMASTER} is absent: the link test is skipped")
    def test_link_puppetmaster(self):
        code, report = self.hp("link", "--repo", str(PUPPETMASTER), "--cases", "20000", "--mutants", "20")
        self.assertEqual(report["verdict"], "agree", json.dumps(report, indent=1))
        self.assertEqual(code, 0)
        self.assertEqual(report["cases"], 20000)
        self.assertEqual(report["differences"], 0)
        self.assertEqual(report["function"], "puppetmaster.registry_sync.plan_starter_sync")
        self.assertTrue(report["mutants"]["identity_copy_agrees"])
        self.assertGreaterEqual(report["mutants"]["killed"], 1)

    def test_laws_ref_gap_and_question(self):
        code, report = self.hp("check", "laws", "ref", "gap")
        self.assertAccept(code, report)
        laws = self.result(report, "laws")
        self.assertEqual(laws["verdict"], "accept")
        self.assertEqual(laws["laws"], LAWS)
        self.assertEqual(self.result(report, "ref")["verdict"], "accept")
        self.assertEqual(self.result(report, "gap")["verdict"], "accept")
        code, report = self.hp("question", "gap")
        self.assertAccept(code, report)
        q = report["question"]
        self.assertEqual(q["input"]["encoded"], "0||1,1,1,0;2,2,2,0|")
        self.assertEqual(q["design_a"]["encoded"], "1,1,1,0;2,2,2,0")
        self.assertEqual(q["design_b"]["encoded"], "2,2,2,0;1,1,1,0")
        self.assertEqual(q["ref"]["encoded"], "1,1,1,0;2,2,2,0")
        self.assertIn("id 2", q["design_b"]["shown"])

    def test_order_law_makes_laws_complete(self):
        self.overlay("order")
        code, report = self.hp("check", "laws")
        self.assertAccept(code, report)
        self.assertEqual(self.result(report, "laws")["laws"], LAWS + ["StarterOrder"])
        code, report = self.hp("check", "complete")
        self.assertAccept(code, report)
        code, report = self.hp("check", "gap")
        self.assertReject(code, report)
        self.assertEqual(self.result(report, "gap")["stage"], "build")

    def test_false_law_gives_conflict(self):
        self.overlay("false_law")
        code, report = self.hp("check", "conflict")
        self.assertAccept(code, report)
        self.assertEqual(self.result(report, "conflict")["law"], "NewAlwaysEnabled")
        code, report = self.hp("check", "ref")
        self.assertReject(code, report)
        code, report = self.hp("question", "conflict")
        self.assertAccept(code, report)
        q = report["question"]
        self.assertEqual(q["law"], "NewAlwaysEnabled")
        self.assertEqual(q["input"]["encoded"], "0||1,1,1,1|")
        self.assertEqual(q["ref"]["encoded"], "1,1,1,0")

    def test_conflict_must_name_a_law(self):
        self.overlay("false_law")
        text = self.read("ConflictSolution.lean").replace("hardproof-law: NewAlwaysEnabled",
                                                          "hardproof-law: NoSuchLaw")
        self.write("ConflictSolution.lean", text)
        code, report = self.hp("check", "conflict")
        self.assertReject(code, report)
        self.assertEqual(self.result(report, "conflict")["stage"], "law")

    def test_broken_kind_does_not_stop_another(self):
        self.write("CompleteSolution.lean", "import Laws\nthis does not parse\n")
        code, report = self.hp("check", "complete", "gap")
        self.assertAccept(code, report)
        self.assertEqual(report["accepted_kind"], "gap")
        self.assertEqual(self.result(report, "complete")["stage"], "build")

    def test_absent_name_is_found_before_the_comparator(self):
        text = self.read("GapSolution.lean").replace("theorem differ", "theorem differs")
        self.write("GapSolution.lean", text)
        code, report = self.hp("check", "gap")
        self.assertReject(code, report)
        res = self.result(report, "gap")
        self.assertEqual(res["stage"], "absent_name")
        self.assertIn("HPGap.differ", res["problems"][0])


if __name__ == "__main__":
    unittest.main()



class QuestionInFreshFolderTest(unittest.TestCase):
    """The question command must work in a folder where the model was not built before."""

    def test_question_builds_the_model(self):
        import shutil
        import tempfile
        from pathlib import Path
        from helpers import run_hp
        src = Path(__file__).resolve().parent.parent / "examples" / "sync"
        with tempfile.TemporaryDirectory() as tmp:
            dst = Path(tmp) / "sync"
            shutil.copytree(src, dst, ignore=shutil.ignore_patterns(".lake", "hp", "variants", "hardproof_runs.jsonl"))
            out = run_hp(dst, "question", "gap")
            report = out[1] if isinstance(out[1], dict) else out[-1]
            self.assertEqual(report.get("verdict"), "accept", report)
            self.assertTrue(report["question"]["input"]["encoded"])
