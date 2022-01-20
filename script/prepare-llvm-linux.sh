#!/usr/bin/env bash
set -uo pipefail

# run from root build directory (from inside nix-shell or otherwise defining GLIBC/ZLIB/GMP) as in
# ```
# eval cmake ../.. $(../../script/prepare-llvm-linux.sh ~/Downloads/lean-llvm-x86_64-linux-gnu.tar.zst)
# ```

# use full LLVM release for compiling C++ code, but subset for compiling C code and distribution

[[ -d llvm ]] || (mkdir llvm; tar xf $1 --strip-components 1 --directory llvm)
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
$CP llvm/lib/lib{c++,c++abi,unwind}.* $GMP/lib/libgmp.a stage1/lib/
# glibc: use for linking (so Lean programs don't embed newer symbol versions), but not for running (because libc.so, librt.so, and ld.so must be compatible)!
$CP $GLIBC/lib/libc_nonshared.a stage1/lib/glibc
for f in $GLIBC/lib/lib{c,dl,m,rt,pthread}-*; do b=$(basename $f); cp $f stage1/lib/glibc/${b%-*}.so; done
OPTIONS=()
echo -n " -DLEAN_STANDALONE=ON"
echo -n " -DCMAKE_C_COMPILER=$PWD/stage1/bin/clang -DCMAKE_CXX_COMPILER=$PWD/llvm/bin/clang++ -DLEAN_CXX_STDLIB='-Wl,-Bstatic -lc++ -lc++abi -Wl,-Bdynamic'"
# allow C++ code to include /usr since it needs quite a few more headers
# set sysroot for clang to make sure we have all necessary runtime files
echo -n " -DLEAN_EXTRA_CXX_FLAGS='--sysroot $PWD/llvm -isystem /usr/include -isystem /usr/include/x86_64-linux-gnu'"
# ... but don't embed in `leanc` so users can still link to system libs, while using `-nostdinc` to make sure headers are not visible by default
# (in particular, not to `#include_next` in the clang headers)
echo -n " -DLEANC_INTERNAL_FLAGS='-nostdinc -isystem ROOT/include/clang' -DLEANC_CC=ROOT/bin/clang"
echo -n " -DLEANC_INTERNAL_LINKER_FLAGS='-L ROOT/lib -L ROOT/lib/glibc ROOT/lib/glibc/libc_nonshared.a -Wl,--as-needed -static-libgcc -Wl,-Bstatic -lgmp -lunwind -Wl,-Bdynamic -fuse-ld=lld'"
# do not set `LEAN_CC` for tests
echo -n " -DLEAN_TEST_VARS=''"
