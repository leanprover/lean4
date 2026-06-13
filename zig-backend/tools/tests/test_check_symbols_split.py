"""Integration tests for the split-runtime symbol checker."""

import os
import re
import subprocess
import sys
import unittest
from pathlib import Path


TOOLS_DIR = Path(__file__).resolve().parent.parent
CHECK_SYMBOLS_PATH = TOOLS_DIR / "check-symbols.sh"
ZB_DIR = Path(__file__).resolve().parents[2]
LEAN4_DIR = Path(os.environ.get("LEAN4_DIR", str(ZB_DIR.parent)))
LEAN_H = LEAN4_DIR / "src/include/lean/lean.h"
UPSTREAM_RUNTIME = LEAN4_DIR / "build/release/stage1/lib/lean/libleanrt.a"


def declared_symbols() -> set[str]:
    """Return one-line LEAN_EXPORT function declarations from lean.h."""
    symbols = set()
    for line in LEAN_H.read_text().splitlines():
        match = re.search(r"^\s*LEAN_EXPORT\b.*\b(lean_[A-Za-z0-9_]+)\s*\(", line)
        if match:
            symbols.add(match.group(1))
    return symbols


def archive_symbols(path: Path) -> set[str]:
    """Return defined lean_* symbols from a static archive."""
    output = subprocess.run(
        ["nm", str(path)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    return {
        re.sub(r"^.* [TDSB] _?", "", line).strip()
        for line in output
        if re.search(r" [TDSB] _?lean_", line)
    }


class TestCheckSymbolsSplit(unittest.TestCase):
    """Tests for tools/check-symbols.sh with split runtime archives."""

    def test_cli_passes_for_split_runtime(self):
        """check-symbols.sh exits 0 and reports zero missing symbols."""
        result = subprocess.run(
            [str(CHECK_SYMBOLS_PATH)],
            cwd=ZB_DIR,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, msg=result.stderr or result.stdout)
        self.assertIn("Missing symbols: 0", result.stdout)
        self.assertIn("libleanrt-zig.a", result.stdout)
        self.assertIn("libleanrt_cpp_partial.a", result.stdout)

    def test_split_runtime_matches_reference_runtime_gap(self):
        """Only symbols missing from the split runtime are already absent upstream."""
        header = declared_symbols()
        combined = archive_symbols(ZB_DIR / "zig-out/lib/libleanrt-zig.a") | archive_symbols(
            ZB_DIR / "zig-out/lib/libleanrt_cpp_partial.a"
        )
        upstream = archive_symbols(UPSTREAM_RUNTIME)

        # The split runtime may export header symbols that the upstream
        # monolithic archive does not (e.g. the allocator hooks reclaimed in
        # M3 and the IO error constructors reclaimed in M5). The invariant is
        # only that nothing is missing from the split runtime unless it is
        # also absent upstream.
        self.assertLessEqual(header - combined, header - upstream)


if __name__ == "__main__":
    unittest.main(verbosity=2)
