"""Regression tests of the lean CODEX_HOME: a removed AGENTS.md and nested arrays in a dropped table."""
from __future__ import annotations

import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

TOOL = Path(__file__).resolve().parent.parent
if str(TOOL) not in sys.path:
    sys.path.insert(0, str(TOOL))

from hpflow import codexhome  # noqa: E402


class PrepareAgentsTest(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.user, self.work = Path(tmp.name) / "user", Path(tmp.name) / "work"
        self.user.mkdir()
        (self.user / "auth.json").write_text("{}", encoding="utf-8")
        env = mock.patch.dict(os.environ, {"CODEX_HOME": str(self.user), "HPFLOW_CODEX_HOME": str(self.work)})
        env.start()
        self.addCleanup(env.stop)
        seed = mock.patch.object(codexhome, "seed_system_skills", lambda home, codex: None)
        seed.start()
        self.addCleanup(seed.stop)

    def test_a_removed_agents_md_leaves_the_lean_home(self) -> None:
        (self.user / "AGENTS.md").write_text("be nice\n", encoding="utf-8")
        codexhome.prepare("codex")
        self.assertTrue((self.work / "AGENTS.md").exists())
        (self.user / "AGENTS.md").unlink()
        codexhome.prepare("codex")
        self.assertFalse((self.work / "AGENTS.md").exists())

    def test_a_kept_agents_md_stays_in_the_lean_home(self) -> None:
        (self.user / "AGENTS.md").write_text("be nice\n", encoding="utf-8")
        codexhome.prepare("codex")
        codexhome.prepare("codex")
        self.assertEqual((self.work / "AGENTS.md").read_text(encoding="utf-8"), "be nice\n")

    def test_no_agents_md_at_all(self) -> None:
        self.assertEqual(codexhome.prepare("codex"), self.work)
        self.assertFalse((self.work / "AGENTS.md").exists())


class LeanConfigTest(unittest.TestCase):
    def test_a_nested_array_in_a_dropped_table_is_dropped(self) -> None:
        text = '[mcp_servers.x]\nargs=[\n["a"],\n]\nk=1\n[t]\na=1\n'
        self.assertEqual(codexhome.lean_config(text), "[t]\na=1\n")

    def test_a_flat_multi_line_array_in_a_dropped_table(self) -> None:
        text = '[mcp_servers.x]\nargs=[\n"a",\n]\nk=1\n[t]\na=1\n'
        self.assertEqual(codexhome.lean_config(text), "[t]\na=1\n")

    def test_a_nested_array_in_a_kept_table_is_kept(self) -> None:
        text = 'model="m"\n[t]\nargs=[\n["a"],\n]\n[mcp_servers.x]\ncommand="c"\n'
        self.assertEqual(codexhome.lean_config(text), 'model="m"\n[t]\nargs=[\n["a"],\n]\n')


if __name__ == "__main__":
    unittest.main()
