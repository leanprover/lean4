#!/usr/bin/env bash
set -euo pipefail

LEAN="${LEAN:-lean}"
TEST="$1"
BASENAME="$(basename "$TEST" .lean)"
OUT="$BASENAME.zig"

# Emit Zig code for the module.
"$LEAN" -Dbackward.do.legacy=false "$TEST" -z "$OUT"

# Basic sanity: the file must be non-empty and mention the module.
[[ -s "$OUT" ]] || { echo "Zig output is empty"; exit 1; }
grep -q "module: ${BASENAME}" "$OUT" || { echo "Missing module marker"; exit 1; }

# Syntactic sanity via zig fmt.
if command -v zig &> /dev/null; then
  zig fmt "$OUT"
  zig ast-check "$OUT"
fi

echo "ok"
