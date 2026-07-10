#!/usr/bin/env bash
# Build a core-runtime-linked Lean wasm module for browser / Node (WASI reactor).
set -euo pipefail
cd "$(dirname "$0")"

ROOT="$(cd ../../.. && pwd)"
LEAN="${LEAN:-$ROOT/build/release/stage1/bin/lean}"
LEANC="${LEANC:-$ROOT/build/release/stage1/bin/leanc}"
export WASI_SDK_PATH="${WASI_SDK_PATH:-$ROOT/build/wasi-sdk}"
STAGE1="${LEAN_BUILD_DIR:-$ROOT/build/release/stage1}"
export PATH="$(dirname "$LEAN"):$PATH"

[[ -x "$LEAN" ]] || { echo "lean not found at $LEAN" >&2; exit 1; }
[[ -n "${WASI_SDK_PATH-}" && -d "$WASI_SDK_PATH" ]] || {
  echo "set WASI_SDK_PATH to an extracted wasi-sdk" >&2
  exit 1
}

if [[ ! -f "$STAGE1/wasm32-wasip1/libleanrt.a" ]]; then
  "$ROOT/script/build_wasm_runtime.sh" "$ROOT/build/release/wasm32-wasip1"
fi

# Reuse the multi-module pure core-runtime test program.
LIB_DIR="_tmp_core_rt_deps"
rm -rf "$LIB_DIR"
mkdir -p "$LIB_DIR"
cp ../core_rt_lib.lean ../core_rt.lean .

lean -o "$LIB_DIR/core_rt_lib.olean" --wasm="$LIB_DIR/core_rt_lib.wasm" core_rt_lib.lean
LEAN_PATH="$LIB_DIR" lean --wasm=core_rt_main.wasm core_rt.lean
leanc --target=wasm32-wasip1 -Wl,--export=lean_wasm_core_rt \
  -o core_rt.wasm "$LIB_DIR/core_rt_lib.wasm" core_rt_main.wasm

wasm-validate --enable-exceptions core_rt.wasm
rm -f core_rt.lean core_rt_lib.lean core_rt_main.wasm
rm -rf "$LIB_DIR"
echo "wrote $(pwd)/core_rt.wasm"
echo "Run: python3 -m http.server 8765  then open core_rt.html"
