#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

ROOT="$(cd ../../.. && pwd)"
LEAN="${LEAN:-$ROOT/build/release/stage1/bin/lean}"
WASM_LD="${WASM_LD:-/opt/homebrew/opt/lld/bin/wasm-ld}"
if [[ ! -x "$WASM_LD" ]]; then
  WASM_LD="$(command -v wasm-ld || true)"
fi
[[ -n "$WASM_LD" && -x "$WASM_LD" ]] || { echo "wasm-ld not found; set WASM_LD" >&2; exit 1; }
[[ -x "$LEAN" ]] || { echo "lean not found at $LEAN; set LEAN" >&2; exit 1; }

OBJ="_tmp_demo.o.wasm"
"$LEAN" --wasm="$OBJ" Demo.lean
"$WASM_LD" --no-entry \
  --export=lean_wasm_demo_add \
  --export=lean_wasm_demo_answer \
  --export=lean_wasm_demo_choose \
  -o demo.wasm "$OBJ"
wasm-validate demo.wasm
rm -f "$OBJ"
echo "wrote $(pwd)/demo.wasm"
