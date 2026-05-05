#!/usr/bin/env bash

# This script must be called from the repo root.
# The radar environment variables must be provided.
# See also the https://github.com/leanprover/radar readme.

LLVM_RELEASE=19.1.2
LLVM_TARBALL="$RADAR_CACHE/llvm/$LLVM_RELEASE.tar.zst"

rm -rf "$RADAR_CACHE/llvm"

if [ ! -f "$LLVM_TARBALL" ]; then
    mkdir -p "$RADAR_CACHE/llvm"
    curl --location -o "$LLVM_TARBALL" "https://github.com/leanprover/lean-llvm/releases/download/$LLVM_RELEASE/lean-llvm-x86_64-linux-gnu.tar.zst"
fi

mkdir -p build/release
cd build/release
eval cmake ../.. \
    --preset release $(../.././script/prepare-llvm-linux.sh /tmp/llvm/19.1.2.tar.zst) \
    -DWFAIL=OFF
cd ../..
make -C build/release -j"$(nproc)" bench-part2
mv tests/part2.measurements.jsonl "$RADAR_OUT"
