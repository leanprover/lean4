#!/usr/bin/env bash
# Experimental: configure/build Lean with the Emscripten CMake toolchain.
# This is the “full Lean as wasm” path (compiler), not the language-core
# `--wasm` object backend. See doc/make/emscripten.md.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="${1:-$root/build/emscripten}"
jobs="${BUILD_JOBS:-$(sysctl -n hw.logicalcpu 2>/dev/null || nproc 2>/dev/null || echo 4)}"

if ! command -v emcc >/dev/null 2>&1; then
  echo "emcc not on PATH; install and activate emsdk first" >&2
  exit 1
fi
if ! command -v emcmake >/dev/null 2>&1; then
  echo "emcmake not on PATH; activate emsdk (source emsdk_env.sh)" >&2
  exit 1
fi

mkdir -p "$out"
if [[ ! -f "$out/CMakeCache.txt" ]]; then
  echo "Configuring Emscripten build in $out"
  # Point at src/ like other builds; stage0 is expected from the native tree.
  (
    cd "$out"
    emcmake cmake "$root/src" \
      -DCMAKE_BUILD_TYPE=Release \
      -DUSE_GMP=OFF \
      -DMMAP=OFF \
      -DLEAN_INSTALL_SUFFIX=-wasm32 \
      ${EMSCRIPTEN_CMAKE_OPTIONS:-}
  )
fi

echo "Building (jobs=$jobs). This may fail until the Emscripten port is fully revived."
set +e
cmake --build "$out" --target lean -j"$jobs"
status=$?
set -e
if [[ $status -ne 0 ]]; then
  echo "Emscripten build failed with status $status (expected while port is incomplete)." >&2
  echo "Native wasm backend + core runtime: script/build_wasm_runtime.sh" >&2
  exit "$status"
fi
echo "Emscripten lean target built under $out"
