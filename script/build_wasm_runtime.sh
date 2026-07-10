#!/usr/bin/env bash
# Build the language-core Lean runtime for wasm32-wasip1 (no IO / libuv / tasks).
#
# Requires:
#   WASI_SDK_PATH  – extracted wasi-sdk (https://github.com/WebAssembly/wasi-sdk/releases)
#   LEAN_BUILD_DIR – stage1 build dir with include/lean (default: $root/build/release/stage1)
#
# Installs libleanrt.a to:
#   $1 (default: $root/build/release/wasm32-wasip1)
#   and $LEAN_BUILD_DIR/wasm32-wasip1 for `leanc --target=wasm32-wasip1`
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
sdk="${WASI_SDK_PATH:?set WASI_SDK_PATH to an extracted wasi-sdk directory}"
out="${1:-$root/build/release/wasm32-wasip1}"
stage1="${LEAN_BUILD_DIR:-$root/build/release/stage1}"

mkdir -p "$out/include/lean" "$out/obj"
printf '%s\n' '#pragma once' '#include <lean/version.h>' '#define LEAN_IS_STAGE0 0' > "$out/include/lean/config.h"

sources=(debug mpz utf8 object apply exception memory alloc mpn native_backend wasm_support)
objects=()
for source in "${sources[@]}"; do
  object="$out/obj/$source.o"
  # wasi-sdk ≥ 22 uses the non-legacy EH scheme by default; older toolchains needed
  # `-mllvm -wasm-use-legacy-eh=false`. Prefer a plain `-fwasm-exceptions` so both work.
  "$sdk/bin/clang++" -std=c++20 -O2 -DNDEBUG -DLEAN_WASI -DLEAN_USE_SPLIT_STACK \
    -fwasm-exceptions \
    -I "$out/include" -I "$stage1/include" -I "$root/src/include" -I "$root/src" \
    -c "$root/src/runtime/$source.cpp" -o "$object"
  objects+=("$object")
done

"$sdk/bin/llvm-ar" rcs "$out/libleanrt.a" "${objects[@]}"

# leanc resolves the archive relative to the Lean sysroot (stage1/).
mkdir -p "$stage1/wasm32-wasip1"
cp -f "$out/libleanrt.a" "$stage1/wasm32-wasip1/libleanrt.a"

printf '%s\n' "$out/libleanrt.a"
