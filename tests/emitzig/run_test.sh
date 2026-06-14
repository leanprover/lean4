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

# End-to-end executable smoke test.
if [[ "${LEAN_ZIG_EXE:-0}" == "1" ]] && command -v zig &>/dev/null; then
  ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
  LEANC="${LEANC:-$ROOT/build/release/stage1/bin/leanc}"
  if [[ -x "$LEANC" ]]; then
    EXE="$BASENAME"
    if [[ "${LEAN_ZIG_ZIGRT:-0}" == "1" ]]; then
      "$ROOT/tools/zigc-zigrt" "$OUT" "$EXE"
    else
      "$ROOT/tools/zigc" "$OUT" "$EXE"
    fi
    "./$EXE"
  fi
fi

echo "ok"

