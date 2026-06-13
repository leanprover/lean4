"""Unit tests for scan-commits.py.

Covers: empty range, backend-touching commit, non-backend commit,
rename detection, delete detection, multi-subsystem, footprint cap,
deterministic re-run, --help, --check.
"""

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Ensure the parent directory (tools/) is on the path so we can import scan_commits.
TOOLS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(TOOLS_DIR))

# Also add the tools dir as a package root for importlib
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

# Import the module from the .py file directly
import importlib.util
import os
spec = importlib.util.spec_from_file_location("scan_commits", str(TOOLS_DIR / "scan-commits.py"))
scan_commits_mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scan_commits_mod)
sc = scan_commits_mod


LEAN4_REPO = Path(os.environ.get("LEAN4_DIR", str(Path(__file__).resolve().parents[3])))
SCANNER_PATH = TOOLS_DIR / "scan-commits.py"


class TestScanCommits(unittest.TestCase):
    """Tests for scan-commits.py functionality."""

    def setUp(self):
        self.tmpdir = Path(tempfile.mkdtemp(prefix="scan_commits_test_"))
        self.addCleanup(shutil.rmtree, self.tmpdir, ignore_errors=True)

    def make_reports_dir(self, name: str) -> Path:
        """Create a temp sync/reports-style directory and return reports path."""
        reports_dir = self.tmpdir / name / "reports"
        reports_dir.mkdir(parents=True)
        return reports_dir

    # ------------------------------------------------------------------
    # CLI tests
    # ------------------------------------------------------------------
    def test_cli_help(self):
        """--help exits 0 and prints usage."""
        result = subprocess.run(
            [sys.executable, str(SCANNER_PATH), "--help"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0)
        self.assertIn("usage:", result.stdout.lower())

    def test_cli_check_missing_reports(self):
        """--check on empty sync dir with a non-empty range returns non-zero."""
        # Use a range that definitely has commits but point to an empty output dir
        empty_dir = self.tmpdir / "empty_sync"
        empty_dir.mkdir()
        result = subprocess.run(
            [sys.executable, str(SCANNER_PATH), "--check", "--since", "0556412f8d", "--to", "HEAD", "--out-dir", str(empty_dir)],
            capture_output=True,
            text=True,
        )
        # --check should fail because no reports exist for the range
        self.assertNotEqual(result.returncode, 0)

    # ------------------------------------------------------------------
    # Core logic tests (using real lean4 repo data)
    # ------------------------------------------------------------------
    def test_empty_range(self):
        """Range with no commits produces manifest with total_commits=0."""
        out_dir = self.make_reports_dir("empty_range")
        manifest = sc.scan_range(
            repo=str(LEAN4_REPO),
            since="HEAD",
            to="HEAD",
            out_dir=out_dir,
        )
        self.assertEqual(manifest["total_commits"], 0)
        self.assertEqual(manifest["backend_touching_commits"], 0)
        self.assertTrue((out_dir.parent / "manifest.json").exists())

    def test_classifies_backend_commit(self):
        """A commit touching src/runtime/ is classified needs_port=true."""
        # 0556412f8d is the backend origin commit — it created src/runtime/
        # Use an isolated subdir so we only see this commit's report
        out = self.make_reports_dir("backend_commit")
        manifest = sc.scan_range(
            repo=str(LEAN4_REPO),
            since="0556412f8d^",
            to="0556412f8d",
            out_dir=out,
        )
        self.assertEqual(manifest["total_commits"], 1)
        self.assertEqual(manifest["backend_touching_commits"], 1)

        reports = list(out.glob("*.json"))
        # manifest.json is also in this dir, filter it out
        reports = [r for r in reports if r.name != "manifest.json"]
        self.assertEqual(len(reports), 1)
        report = json.loads(reports[0].read_text())
        self.assertTrue(report["needs_port"])
        self.assertIn("backend_changes", report)
        self.assertTrue(len(report["backend_changes"]) > 0)
        self.assertIsInstance(report.get("zig_target"), dict)
        self.assertTrue(report["zig_target"])
        # Verify zig_target mapping exists for each change
        for ch in report["backend_changes"]:
            self.assertIn("zig_target", ch)
            self.assertEqual(report["zig_target"][ch["path"]], ch["zig_target"])
        self.assertTrue((out.parent / "manifest.json").exists())

    def test_classifies_non_backend_commit(self):
        """A commit touching only doc/ is classified needs_port=false."""
        # Find a commit that only touches doc/ by scanning a small range
        # We'll use a known doc-only commit: search backwards from HEAD for one
        # that only touches doc/ or *.md files.
        # Instead, we test the logic directly with a mocked diff.
        diff_text = "M\tdoc/what_is_lean4.md\n"
        changes = sc.parse_diff(diff_text)
        self.assertEqual(len(changes), 1)
        self.assertFalse(sc.is_backend_change(changes[0]["path"]))

    def test_rename_detection(self):
        """A renamed file is recorded with status=R and both old/new paths."""
        diff_text = "R100\told/path.cpp\tnew/path.cpp\n"
        changes = sc.parse_diff(diff_text)
        self.assertEqual(len(changes), 1)
        self.assertEqual(changes[0]["status"], "R")
        self.assertEqual(changes[0]["path"], "new/path.cpp")
        self.assertEqual(changes[0].get("old_path"), "old/path.cpp")

    def test_delete_detection(self):
        """A deleted backend file is recorded with status=D."""
        diff_text = "D\tsrc/runtime/object.cpp\n"
        changes = sc.parse_diff(diff_text)
        self.assertEqual(len(changes), 1)
        self.assertEqual(changes[0]["status"], "D")
        self.assertEqual(changes[0]["path"], "src/runtime/object.cpp")
        self.assertTrue(sc.is_backend_change(changes[0]["path"]))

    def test_multi_subsystem(self):
        """Commit touching runtime + IR is reflected in counts_per_subsystem."""
        diff_text = (
            "M\tsrc/runtime/object.cpp\n"
            "M\tsrc/Lean/Compiler/IR/Basic.lean\n"
        )
        changes = sc.parse_diff(diff_text)
        subsystems = sc.classify_subsystems(changes)
        self.assertIn("runtime", subsystems)
        self.assertIn("compiler_ir", subsystems)

    def test_footprint_cap(self):
        """Per-report JSON ≤ 10 KB even for commits with many changes."""
        # Simulate a commit with many backend changes
        lines = [f"M\tsrc/runtime/object_{i:04d}.cpp\n" for i in range(5000)]
        diff_text = "".join(lines)
        changes = sc.parse_diff(diff_text)
        report = sc.build_report(
            sha="a" * 40,
            short_sha="abcdef1234",
            subject="big commit",
            author="test",
            date="2024-01-01",
            changes=changes,
            max_kb=10,
        )
        raw = json.dumps(report, sort_keys=True, indent=2)
        self.assertLessEqual(len(raw.encode("utf-8")), 10 * 1024)
        if len(changes) > 0:
            self.assertTrue(report.get("truncated", False))

    def test_deterministic_rerun(self):
        """Running twice produces byte-identical top-level manifest.json."""
        out = self.make_reports_dir("rerun")

        sc.scan_range(
            repo=str(LEAN4_REPO),
            since="0556412f8d",
            to="0556412f8d",
            out_dir=out,
        )
        manifest_path = out.parent / "manifest.json"
        first_bytes = manifest_path.read_bytes()

        sc.scan_range(
            repo=str(LEAN4_REPO),
            since="0556412f8d",
            to="0556412f8d",
            out_dir=out,
        )
        second_bytes = manifest_path.read_bytes()
        self.assertEqual(first_bytes, second_bytes)

    def test_cli_real_run_writes_top_level_manifest(self):
        """CLI run writes sync/manifest.json alongside sync/reports/."""
        out_dir = self.make_reports_dir("cli_real_run")
        result = subprocess.run(
            [
                sys.executable,
                str(SCANNER_PATH),
                "--since",
                "0556412f8d",
                "--to",
                "0556412f8d^0",
                "--out-dir",
                str(out_dir),
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertTrue((out_dir.parent / "manifest.json").exists())
        self.assertTrue((out_dir / "0556412f8d.json").exists())

    def test_simple_since_is_inclusive(self):
        """A simple --since revision is included in the scan range."""
        out_dir = self.make_reports_dir("inclusive_since")
        manifest = sc.scan_range(
            repo=str(LEAN4_REPO),
            since="0556412f8d",
            to="0556412f8d^0",
            out_dir=out_dir,
        )
        self.assertEqual(manifest["total_commits"], 1)
        self.assertTrue((out_dir / "0556412f8d.json").exists())

    def test_report_fields(self):
        """Sampled report has all required fields."""
        out = self.make_reports_dir("report_fields")
        sc.scan_range(
            repo=str(LEAN4_REPO),
            since="0556412f8d^",
            to="0556412f8d",
            out_dir=out,
        )
        reports = [r for r in out.glob("*.json") if r.name != "manifest.json"]
        self.assertTrue(len(reports) > 0)
        report = json.loads(reports[0].read_text())
        for field in ("sha", "short_sha", "subject", "author", "date", "needs_port", "backend_changes", "zig_target"):
            self.assertIn(field, report)
        self.assertIsInstance(report["zig_target"], dict)
        for ch in report["backend_changes"]:
            for field in ("path", "status", "zig_target"):
                self.assertIn(field, ch)
            self.assertIn(ch["status"], ("A", "M", "D", "R"))
            self.assertEqual(report["zig_target"][ch["path"]], ch["zig_target"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
