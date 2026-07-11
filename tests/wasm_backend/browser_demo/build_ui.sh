#!/usr/bin/env bash
# Build the Lean fiber UI demo (core runtime + ui.wasm).
set -euo pipefail
cd "$(dirname "$0")"

ROOT="$(cd ../../.. && pwd)"
LEAN="${LEAN:-$ROOT/build/release/stage1/bin/lean}"
export WASI_SDK_PATH="${WASI_SDK_PATH:-$ROOT/build/wasi-sdk}"
STAGE1="${LEAN_BUILD_DIR:-$ROOT/build/release/stage1}"
export PATH="$(dirname "$LEAN"):$PATH"

[[ -x "$LEAN" ]] || { echo "lean not found at $LEAN" >&2; exit 1; }
[[ -d "${WASI_SDK_PATH}" ]] || { echo "set WASI_SDK_PATH" >&2; exit 1; }

if [[ ! -f "$STAGE1/wasm32-wasip1/libleanrt.a" ]]; then
  "$ROOT/script/build_wasm_runtime.sh" "$ROOT/build/release/wasm32-wasip1"
fi

# Rebuild runtime so ui bridge symbols are present
"$ROOT/script/build_wasm_runtime.sh" "$ROOT/build/release/wasm32-wasip1"

OBJ="_tmp_ui.o.wasm"
(cd .. && lean -o browser_demo/UiAbi.olean --wasm=browser_demo/_tmp_ui_abi.o.wasm UiAbi.lean)
LEAN_PATH="$(pwd):${LEAN_PATH-}" lean --wasm="$OBJ" UiApp.lean
# Generous linear memory + stack: small defaults (2 pages) are tight for
# proof-state UI (strings + history) and some browsers trap as OOB on grow.
leanc --target=wasm32-wasip1 \
  -Wl,--export=lean_ui_boot \
  -Wl,--export=lean_ui_dispatch \
  -Wl,--export=lean_ui_batch \
  -Wl,--export=lean_ui_event_ptr \
  -Wl,--export=lean_ui_event_capacity \
  -Wl,--export=lean_ui_boot_effect_count \
  -Wl,--export=lean_ui_smoke_click \
  -Wl,--initial-memory=16777216 \
  -Wl,--max-memory=268435456 \
  -Wl,--allow-undefined \
  -Wl,-z,stack-size=2097152 \
  -o ui.wasm _tmp_ui_abi.o.wasm "$OBJ"
wasm-validate --enable-exceptions ui.wasm
node ui_abi_smoke.mjs
rm -f "$OBJ" _tmp_ui_abi.o.wasm UiAbi.ir UiAbi.ir.sig UiAbi.olean UiAbi.ilean \
  UiAbi.olean.private UiAbi.olean.server
echo "wrote $(pwd)/ui.wasm"
echo "open ui.html via: python3 -m http.server 8765"
