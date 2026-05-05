#!/usr/bin/env nix
#! nix develop ..#oldGlibc --command /usr/bin/env bash

# This script must be called from the repo root.
# The radar environment variables must be provided.
# See also the https://github.com/leanprover/radar readme.

LLVM_RELEASE=19.1.2
LLVM_TARBALL="$RADAR_CACHE/llvm/$LLVM_RELEASE.tar.zst"

if [ ! -f "$LLVM_TARBALL" ]; then
    mkdir -p "$RADAR_CACHE/llvm"
    curl --location -o "$LLVM_TARBALL" "https://github.com/leanprover/lean-llvm/releases/download/$LLVM_RELEASE/lean-llvm-x86_64-linux-gnu.tar.zst"
fi

mkdir -p build/release
cd build/release
eval cmake ../.. \
    --preset release $(../../script/prepare-llvm-linux.sh $LLVM_TARBALL) \
    -DWFAIL=OFF
rm -rf stage2
cp -r stage1 stage2
rm -rf stage3
cp -r stage1 stage3
cd ../..
make -C build/release -j"$(nproc)" bench-part2
mv tests/part2.measurements.jsonl "$RADAR_OUT"
