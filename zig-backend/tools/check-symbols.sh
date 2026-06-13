#!/usr/bin/env bash
# check-symbols.sh — Verify the combined split-runtime symbol surface against lean.h
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZB_DIR="$(dirname "$SCRIPT_DIR")"
LEAN4_DIR="${LEAN4_DIR:-$(dirname "$ZB_DIR")}"
LEAN_H="${LEAN4_DIR}/src/include/lean/lean.h"
ZIG_LIB="${ZB_DIR}/zig-out/lib/libleanrt-zig.a"
CPP_PARTIAL_LIB="${ZB_DIR}/zig-out/lib/libleanrt_cpp_partial.a"

REFERENCE_CANDIDATES=(
    "${LEAN4_DIR}/build/release/stage1/lib/lean/libleanrt.a"
    "${LEAN4_DIR}/build/release/lib/lean/libleanrt.a"
    "${LEAN4_DIR}/build/release/stage1/lib/libleanrt.a"
    "${LEAN4_DIR}/build/release/lib/libleanrt.a"
)

for path in "$LEAN_H" "$ZIG_LIB" "$CPP_PARTIAL_LIB"; do
    if [[ ! -f "$path" ]]; then
        echo "ERROR: $path not found. Run 'zig build' first." >&2
        exit 1
    fi
done

REFERENCE_LIB=""
for candidate in "${REFERENCE_CANDIDATES[@]}"; do
    if [[ -f "$candidate" ]]; then
        REFERENCE_LIB="$candidate"
        break
    fi
done

if [[ -z "$REFERENCE_LIB" ]]; then
    echo "ERROR: could not locate upstream libleanrt.a under build/release/." >&2
    exit 1
fi

python3 - "$LEAN_H" "$ZIG_LIB" "$CPP_PARTIAL_LIB" "$REFERENCE_LIB" <<'PY'
import re
import subprocess
import sys
from pathlib import Path

lean_h = Path(sys.argv[1])
zig_lib = Path(sys.argv[2])
cpp_partial_lib = Path(sys.argv[3])
reference_lib = Path(sys.argv[4])


def declared_symbols(header: Path) -> list[str]:
    symbols: set[str] = set()
    for line in header.read_text().splitlines():
        match = re.search(r"^\s*LEAN_EXPORT\b.*\b(lean_[A-Za-z0-9_]+)\s*\(", line)
        if match:
            symbols.add(match.group(1))
    return sorted(symbols)


def exported_symbols(archive: Path) -> set[str]:
    output = subprocess.run(
        ["nm", str(archive)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    return {
        re.sub(r"^.* [TDSB] _?", "", line).strip()
        for line in output
        if re.search(r" [TDSB] _?lean_", line)
    }


header_symbols = declared_symbols(lean_h)
zig_symbols = exported_symbols(zig_lib)
cpp_symbols = exported_symbols(cpp_partial_lib)
combined_symbols = zig_symbols | cpp_symbols
reference_symbols = exported_symbols(reference_lib)

required_symbols = sorted(
    sym for sym in header_symbols if sym in combined_symbols or sym in reference_symbols
)
excluded_symbols = sorted(sym for sym in header_symbols if sym not in required_symbols)
missing_symbols = sorted(sym for sym in required_symbols if sym not in combined_symbols)

print(f"lean.h LEAN_EXPORT declarations: {len(header_symbols)}")
print(f"Combined split archives checked: {zig_lib.name} + {cpp_partial_lib.name}")
print(f"Reference monolithic archive: {reference_lib}")
print(f"Symbols in {zig_lib.name}: {len(zig_symbols)}")
print(f"Symbols in {cpp_partial_lib.name}: {len(cpp_symbols)}")
print(f"Combined public lean_* symbols: {len(combined_symbols)}")
print(f"Runtime-required header symbols: {len(required_symbols)}")
print(f"Excluded non-archive declarations: {len(excluded_symbols)}")
if excluded_symbols:
    print("Excluded declarations:")
    for sym in excluded_symbols:
        print(f"  {sym}")

print(f"Missing symbols: {len(missing_symbols)}")
for sym in missing_symbols:
    print(f"MISSING: {sym}", file=sys.stderr)

if missing_symbols:
    sys.exit(1)

print(
    "PASS: Combined split runtime archives cover all runtime-required "
    "LEAN_EXPORT symbols from lean.h"
)
PY
