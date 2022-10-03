#!/usr/bin/env bash
set -uo pipefail

# run from root build directory (from inside nix-shell or otherwise defining GLIBC/ZLIB/GMP) as in
# ```
# eval cmake ../.. $(../../script/prepare-llvm-linux.sh ~/Downloads/lean-llvm-x86_64-linux-gnu.tar.zst)
# ```

# use full LLVM release for compiling C++ code, but subset for compiling C code and distribution

[[ -d llvm ]] || (mkdir llvm; tar xf $1 --strip-components 1 --directory llvm)
[[ -d llvm-host ]] || if [[ "$#" -gt 1 ]]; then
  (mkdir llvm-host; tar xf $2 --strip-components 1 --directory llvm-host)
else
  ln -s llvm llvm-host
fi
mkdir -p stage1/{bin,lib,lib/glibc,include/clang}
CP="cp -d"  # preserve symlinks
# a C compiler!
cp -L llvm/bin/clang stage1/bin/
# a linker!
cp -L llvm/bin/ld.lld stage1/bin/
# a static archiver!
cp -L llvm/bin/llvm-ar stage1/bin/
# dependencies of the above
$CP llvm/lib/lib{clang-cpp,LLVM}*.so* stage1/lib/
$CP $ZLIB/lib/libz.so* stage1/lib/
find stage1 -type f -exec strip --strip-unneeded '{}' \; 2> /dev/null
# lean.h dependencies
$CP llvm/lib/clang/*/include/{std*,__std*,limits}.h stage1/include/clang
# ELF dependencies, must be put there for `--sysroot`
$CP $GLIBC/lib/crt* llvm/lib/
$CP $GLIBC/lib/crt* stage1/lib/
# runtime
(cd llvm; $CP --parents lib/clang/*/lib/*/{clang_rt.*.o,libclang_rt.builtins*} ../stage1)
$CP llvm/lib/x86_64-unknown-linux-gnu/lib{c++,c++abi,unwind}.* $GMP/lib/libgmp.a stage1/lib/
# LLVM 15 appears to ship the dependencies in
# `llvm/lib/x86_64-unknown-linux-gnu`, but clang-15 that we use to compile is
# linked in such a way that it assumes the path is at `llvm/lib/`
$CP llvm/lib/x86_64-unknown-linux-gnu/lib{c++,c++abi,unwind}.* llvm/lib/
# glibc: use for linking (so Lean programs don't embed newer symbol versions), but not for running (because libc.so, librt.so, and ld.so must be compatible)!
$CP $GLIBC/lib/libc_nonshared.a stage1/lib/glibc
for f in $GLIBC/lib/lib{c,dl,m,rt,pthread}-*; do b=$(basename $f); cp $f stage1/lib/glibc/${b%-*}.so; done
OPTIONS=()
echo -n " -DLEAN_STANDALONE=ON"
echo -n " -DCMAKE_CXX_COMPILER=$PWD/llvm-host/bin/clang++ -DLEAN_CXX_STDLIB='-Wl,-Bstatic -lc++ -lc++abi -Wl,-Bdynamic'"
echo -n " -DLEAN_EXTRA_CXX_FLAGS='--sysroot $PWD/llvm -idirafter $GLIBC_DEV/include ${EXTRA_FLAGS:-}'"
# use target compiler directly when not cross-compiling
if [[ -L llvm-host ]]; then
  echo -n " -DCMAKE_C_COMPILER=$PWD/stage1/bin/clang"
else
  echo -n " -DCMAKE_C_COMPILER=$PWD/llvm-host/bin/clang -DLEANC_OPTS='--sysroot $PWD/stage1 -resource-dir $PWD/stage1/lib/clang/14.0.0 ${EXTRA_FLAGS:-}'"
fi
# use `-nostdinc` to make sure headers are not visible by default (in particular, not to `#include_next` in the clang headers),
# but do not change sysroot so users can still link against system libs
echo -n " -DLEANC_INTERNAL_FLAGS='-nostdinc -isystem ROOT/include/clang' -DLEANC_CC=ROOT/bin/clang"
echo -n " -DLEANC_INTERNAL_LINKER_FLAGS='-L ROOT/lib -L ROOT/lib/glibc ROOT/lib/glibc/libc_nonshared.a -Wl,--as-needed -static-libgcc -Wl,-Bstatic -lgmp -lunwind -Wl,-Bdynamic -Wl,--no-as-needed -fuse-ld=lld'"
# when not using the above flags, link GMP dynamically/as usual
echo -n " -DLEAN_EXTRA_LINKER_FLAGS='-Wl,--as-needed -lgmp -Wl,--no-as-needed'"
# do not set `LEAN_CC` for tests
echo -n " -DLEAN_TEST_VARS=''"
