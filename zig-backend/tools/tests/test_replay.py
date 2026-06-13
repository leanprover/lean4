"""Unit tests for replay.py.

Covers: --help, single SHA replay, range replay, markdown structure,
Files Changed section, Translation Notes section, non-trivial change detection.
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(TOOLS_DIR))

import importlib.util
spec = importlib.util.spec_from_file_location("replay", str(TOOLS_DIR / "replay.py"))
replay_mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay_mod)
replay = replay_mod

LEAN4_REPO = Path(os.environ.get("LEAN4_DIR", str(Path(__file__).resolve().parents[3])))
REPLAY_PATH = TOOLS_DIR / "replay.py"


class TestReplay(unittest.TestCase):
    """Tests for replay.py functionality."""

    def setUp(self):
        self.tmpdir = Path(tempfile.mkdtemp(prefix="replay_test_"))
        self.addCleanup(shutil.rmtree, self.tmpdir, ignore_errors=True)

    # ------------------------------------------------------------------
    # CLI tests
    # ------------------------------------------------------------------
    def test_cli_help(self):
        """--help exits 0 and prints usage."""
        result = subprocess.run(
            [sys.executable, str(REPLAY_PATH), "--help"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0)
        self.assertIn("usage:", result.stdout.lower())

    def test_cli_single_sha(self):
        """replay.py <sha> produces a markdown file >= 500 bytes."""
        out_dir = self.tmpdir / "replays"
        out_dir.mkdir()
        result = subprocess.run(
            [sys.executable, str(REPLAY_PATH), "0556412f8d", "--out-dir", str(out_dir)],
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        md_files = list(out_dir.glob("*.md"))
        self.assertTrue(len(md_files) > 0, "Expected at least one .md file")
        for f in md_files:
            self.assertGreaterEqual(f.stat().st_size, 500, f"{f.name} too small")

    def test_cli_range(self):
        """replay.py --range <sha1>..<sha2> produces multiple markdown files."""
        out_dir = self.tmpdir / "replays_range"
        out_dir.mkdir()
        result = subprocess.run(
            [sys.executable, str(REPLAY_PATH), "--range", "0556412f8d..0556412f8d",
             "--out-dir", str(out_dir)],
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        md_files = list(out_dir.glob("*.md"))
        self.assertTrue(len(md_files) >= 1)

    # ------------------------------------------------------------------
    # Core logic tests
    # ------------------------------------------------------------------
    def test_find_previous_backend_commit(self):
        """find_previous_backend_commit returns a valid SHA for a known commit."""
        prev = replay.find_previous_backend_commit(str(LEAN4_REPO), "e09155b6f9")
        self.assertIsNotNone(prev)
        self.assertEqual(len(prev), 40)  # full SHA

    def test_get_commit_metadata(self):
        """get_commit_metadata returns required fields."""
        meta = replay.get_commit_metadata(str(LEAN4_REPO), "0556412f8d")
        self.assertIn("sha", meta)
        self.assertIn("short_sha", meta)
        self.assertIn("subject", meta)
        self.assertIn("author", meta)
        self.assertIn("date", meta)
        self.assertEqual(meta["short_sha"], "0556412f8d")

    def test_markdown_has_files_changed_section(self):
        """Generated markdown contains a 'Files Changed' section with status and zig_target."""
        out_dir = self.tmpdir / "replays_section"
        out_dir.mkdir()
        replay.main(["0556412f8d", "--out-dir", str(out_dir), "--repo", str(LEAN4_REPO)])
        md_files = list(out_dir.glob("*.md"))
        self.assertTrue(len(md_files) > 0)
        content = md_files[0].read_text()
        self.assertIn("Files Changed", content)
        # Should contain a table-like structure with status and zig_target
        self.assertIn("Status", content)
        self.assertIn("Zig Target", content)

    def test_markdown_has_translation_notes(self):
        """Generated markdown contains a 'Translation Notes' section."""
        out_dir = self.tmpdir / "replays_notes"
        out_dir.mkdir()
        replay.main(["0556412f8d", "--out-dir", str(out_dir), "--repo", str(LEAN4_REPO)])
        md_files = list(out_dir.glob("*.md"))
        self.assertTrue(len(md_files) > 0)
        content = md_files[0].read_text()
        self.assertIn("Translation Notes", content)

    def test_detect_struct_defs(self):
        """detect_non_trivial_changes flags struct definitions."""
        diff_lines = [
            "+struct lean_object {",
            "+    int m_rc;",
            " };",
        ]
        notes = replay.detect_non_trivial_changes(diff_lines)
        self.assertTrue(any("struct" in n.lower() for n in notes))

    def test_detect_exported_symbols(self):
        """detect_non_trivial_changes flags LEAN_EXPORT additions."""
        diff_lines = [
            "+LEAN_EXPORT lean_object* lean_box(size_t n);",
        ]
        notes = replay.detect_non_trivial_changes(diff_lines)
        self.assertTrue(any("lean_box" in n for n in notes))

    def test_detect_removed_symbols(self):
        """detect_non_trivial_changes flags removed function definitions."""
        diff_lines = [
            "-LEAN_EXPORT void lean_inc(lean_object* o);",
        ]
        notes = replay.detect_non_trivial_changes(diff_lines)
        self.assertTrue(any("removed" in n.lower() for n in notes))

    def test_markdown_has_commit_metadata_header(self):
        """Generated markdown contains commit metadata header."""
        out_dir = self.tmpdir / "replays_meta"
        out_dir.mkdir()
        replay.main(["0556412f8d", "--out-dir", str(out_dir), "--repo", str(LEAN4_REPO)])
        md_files = list(out_dir.glob("*.md"))
        self.assertTrue(len(md_files) > 0)
        content = md_files[0].read_text()
        self.assertIn("0556412f8d", content)
        self.assertIn("Author", content)
        self.assertIn("Date", content)


if __name__ == "__main__":
    unittest.main(verbosity=2)
