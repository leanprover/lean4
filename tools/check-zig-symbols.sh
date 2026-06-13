#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN="${LEAN:-$ROOT/build/release/stage1/bin/lean}"

# Locate the Lean runtime shared library.
if [[ "$OSTYPE" == "darwin"* ]]; then
  LIB="$ROOT/build/release/stage1/lib/lean/libleanshared.dylib"
else
  LIB="$ROOT/build/release/stage1/lib/lean/libleanshared.so"
fi

if [[ ! -f "$LIB" ]]; then
  echo "check-zig-symbols: runtime library not found at $LIB"
  exit 1
fi

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

# Emit Zig for the smoke test; it exercises a broad cross-section of runtime externs.
"$LEAN" -Dbackward.do.legacy=false "$ROOT/tests/emitzig/Smoke.lean" -z "$TMP_DIR/smoke.zig"

# Extract extern function names referenced by the emitted Zig.
grep -oE 'extern fn lean_[A-Za-z0-9_]+' "$TMP_DIR/smoke.zig" | sed 's/extern fn //' | sort -u > "$TMP_DIR/needed.txt"

# Defined symbols exported from the C runtime shared library.
nm -D "$LIB" 2> /dev/null | awk '$2 == "T" || $2 == "t" {print $3}' | sed 's/^_//' | sort -u > "$TMP_DIR/defined.txt" || \
nm "$LIB" | awk '$2 == "T" || $2 == "t" {print $3}' | sed 's/^_//' | sort -u > "$TMP_DIR/defined.txt"

# Symbols provided by the in-tree Zig runtime source files.
grep -rhoE '(export|pub) fn lean_[A-Za-z0-9_]+' "$ROOT/src/runtime/zig" | sed 's/.* fn //' | sort -u > "$TMP_DIR/zig_provided.txt"

# Combine C runtime and Zig runtime coverage.
 sort -u "$TMP_DIR/defined.txt" "$TMP_DIR/zig_provided.txt" > "$TMP_DIR/available.txt"

# Symbols referenced but not covered by either runtime.
comm -23 "$TMP_DIR/needed.txt" "$TMP_DIR/available.txt" > "$TMP_DIR/missing.txt"

# Known inline C runtime functions not yet exported from the Zig runtime.
KNOWN_MISSING=(
  lean_closure_set
  lean_del_object
)

# Remove known missing symbols from the report.
for sym in "${KNOWN_MISSING[@]}"; do
  sed -i.bak "/^$sym$/d" "$TMP_DIR/missing.txt" 2>/dev/null || true
done
rm -f "$TMP_DIR/missing.txt.bak"

COUNT="$(grep -c '^lean_' "$TMP_DIR/missing.txt" || true)"

if [[ "$COUNT" -eq 0 ]]; then
  echo "Missing symbols: 0"
  exit 0
else
  echo "Missing symbols: $COUNT"
  cat "$TMP_DIR/missing.txt"
  exit 1
fi
