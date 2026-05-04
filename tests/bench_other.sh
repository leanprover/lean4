#!/usr/bin/env bash

# This script must be called from the repo root.
# The radar environment variables must be provided.
# See also the https://github.com/leanprover/radar readme.

LLVM_RELEASE=19.1.2
LLVM_BASE_DIR="$RADAR_CACHE/llvm/$LLVM_RELEASE"
LLVM_DIR="$LLVM_BASE_DIR/lean-llvm"
LLVM_TARBALL="$RADAR_CACHE/llvm/$LLVM_RELEASE.tar.zst"

if [ ! -f "$LLVM_TARBALL" ]; then
    mkdir -p "$RADAR_CACHE/llvm"
    curl --location -o "$LLVM_TARBALL" "https://github.com/leanprover/lean-llvm/releases/download/$LLVM_RELEASE/lean-llvm-x86_64-linux-gnu.tar.zst"
    mkdir -p "$LLVM_BASE_DIR"
    tar -I zstd -xf "$LLVM_TARBALL" -C "$LLVM_BASE_DIR"
fi

export LD_LIBRARY_PATH="$LLVM_DIR/lib/x86_64-unknown-linux-gnu:$LD_LIBRARY_PATH"
export PATH="$LLVM_DIR/bin:$PATH"

cmake --preset release -DWFAIL=OFF \
  -DCMAKE_C_COMPILER="$LLVM_DIR/bin/clang" \
  -DCMAKE_CXX_COMPILER="$LLVM_DIR/bin/clang++" \
  -DLLVM_CONFIG="$LLVM_DIR/bin/llvm-config"
make -C build/release -j"$(nproc)" bench-part2
mv tests/part2.measurements.jsonl "$RADAR_OUT"
