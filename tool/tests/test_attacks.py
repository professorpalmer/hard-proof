"""Attacks on the gate, on the example `examples/sync`. Each one must be rejected."""
from __future__ import annotations

import hashlib
import unittest

from helpers import DomainCase

REF_HEAD = "import Types\nimport Ref\nimport Laws\n\nopen HP\n\nnamespace HPRef\n\n"
REF_TAIL = "\nend HPRef\n"


class AttackTest(DomainCase):
    example = "sync"

    def ref_solution(self, body: str) -> None:
        self.write("RefPassesSolution.lean", REF_HEAD + body + REF_TAIL)
        self.remove("GapSolution.lean")

    def assertComparatorRejects(self, kind: str) -> dict:
        code, report = self.hp("check", kind)
        self.assertReject(code, report)
        res = self.result(report, kind)
        self.assertEqual(res["stage"], "comparator", res)
        return res

    def test_sorry_in_solution(self):
        self.ref_solution("theorem ref_passes : Passes ref := sorry\n")
        self.assertComparatorRejects("ref")

    def test_new_axiom(self):
        self.ref_solution("axiom cheat : Passes ref\n\ntheorem ref_passes : Passes ref := cheat\n")
        self.assertComparatorRejects("ref")

    def test_native_decide(self):
        text = self.read("GapSolution.lean")
        self.assertIn("theorem input_legal : Legal input := rfl", text)
        text = text.replace("theorem input_legal : Legal input := rfl",
                            "theorem input_legal : Legal input := by unfold Legal; native_decide")
        self.write("GapSolution.lean", text)
        self.assertComparatorRejects("gap")

    def test_different_statement(self):
        self.ref_solution("theorem ref_passes : KeepsRows ref := fun x => ⟨_, rfl⟩\n")
        self.assertComparatorRejects("ref")

    def test_own_passes_definition(self):
        # The solution does not import Laws. It defines its own, empty `HP.Passes`.
        self.write("RefPassesSolution.lean",
                   "import Types\nimport Ref\n\nnamespace HP\ndef Passes (_ : Impl) : Prop := True\nend HP\n\n"
                   "namespace HPRef\ntheorem ref_passes : HP.Passes HP.ref := trivial\nend HPRef\n")
        self.remove("GapSolution.lean")
        self.assertComparatorRejects("ref")

    def test_laws_import_ref(self):
        text = self.read("Laws.lean").replace("import Types\n", "import Types\nimport Ref\n", 1)
        self.write("Laws.lean", text)
        code, report = self.hp("check", "laws")
        self.assertReject(code, report)
        res = self.result(report, "laws")
        self.assertEqual(res["stage"], "text")
        self.assertTrue(any("import" in p for p in res["problems"]), res)

    def test_laws_name_ref(self):
        text = self.read("Laws.lean").replace(
            "def Passes (f : Impl) : Prop :=",
            "def IsRef (f : Impl) : Prop := ∀ x, f x = HP.ref x\n\ndef Passes (f : Impl) : Prop :=", 1)
        self.write("Laws.lean", text)
        code, report = self.hp("check", "laws")
        self.assertReject(code, report)
        res = self.result(report, "laws")
        self.assertEqual(res["stage"], "text")
        self.assertTrue(any("`ref`" in p for p in res["problems"]), res)

    def test_laws_sorry(self):
        text = self.read("Laws.lean")
        start = text.index("theorem some_design_fails")
        self.write("Laws.lean", text[:start] + "theorem some_design_fails : ∃ f : Impl, ¬ Passes f := sorry\n\nend HP\n")
        code, report = self.hp("check", "laws")
        self.assertReject(code, report)

    def test_edited_pinned_file(self):
        code, report = self.hp("pin")
        self.assertEqual(code, 0)
        code, report = self.hp("verify-pins")
        self.assertAccept(code, report)
        sha = report and hashlib.sha256((self.dir / "Ref.lean").read_bytes()).hexdigest()
        code, report = self.hp("verify-pins", "--expect", f"Ref.lean={sha}")
        self.assertAccept(code, report)
        self.write("Ref.lean", self.read("Ref.lean") + "\n-- an edit after the pin\n")
        code, report = self.hp("verify-pins")
        self.assertReject(code, report)
        self.assertEqual([c["file"] for c in report["changed"]], ["Ref.lean"])
        code, report = self.hp("verify-pins", "--expect", f"Ref.lean={sha}")
        self.assertReject(code, report)

    def test_edited_challenge_is_written_again(self):
        # A changed challenge cannot weaken a check: the tool writes it again first.
        self.write("hp/HPRefChallenge.lean", "import Types\nnamespace HPRef\ntheorem ref_passes : True := sorry\nend HPRef\n")
        self.ref_solution("theorem ref_passes : True := trivial\n")
        code, report = self.hp("check", "ref")
        self.assertReject(code, report)
        self.assertIn("Passes ref", self.read("hp/HPRefChallenge.lean"))


if __name__ == "__main__":
    unittest.main()
