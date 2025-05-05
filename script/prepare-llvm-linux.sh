#!/usr/bin/env bash
set -euxo pipefail

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
mkdir -p stage0/lib
mkdir -p stage1/{bin,lib,include/clang}
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
# also copy USE_LLVM deps into stage 0
$CP llvm/lib/libLLVM*.so* $ZLIB/lib/libz.so* stage0/lib/
# general clang++ dependency, breaks cross-library C++ exceptions if linked statically
$CP $GCC_LIB/lib/libgcc_s.so* stage1/lib/
# bundle libatomic (referenced by LLVM >= 15, and required by the lean executable to run)
$CP $GCC_LIB/lib/libatomic.so* stage1/lib/

find stage1 -type f -exec strip --strip-unneeded '{}' \; 2> /dev/null
# lean.h dependencies
$CP llvm/lib/clang/*/include/{std*,__std*,limits}.h stage1/include/clang
# runtime
(cd llvm; $CP --parents lib/clang/*/lib/*/{clang_rt.*.o,libclang_rt.builtins*} ../stage1)
$CP llvm/lib/*/lib{c++,c++abi,unwind}.* $GMP/lib/libgmp.a $LIBUV/lib/libuv.a stage1/lib/
# LLVM 19 appears to ship the dependencies in 'llvm/lib/<target-triple>/' and 'llvm/include/<target-triple>/'
# but clang-19 that we use to compile is linked against 'llvm/lib/' and 'llvm/include'
# https://github.com/llvm/llvm-project/issues/54955
$CP llvm/lib/*/lib{c++,c++abi,unwind}.* llvm/lib/
$CP llvm-host/lib/*/lib{c++,c++abi,unwind}.* llvm-host/lib/
# libc++ headers are looked up in the host compiler's root, so copy over target-specific includes
$CP -r llvm/include/*-*-* llvm-host/include/ || true
OPTIONS=()
# We build cadical using the custom toolchain on Linux to avoid glibc versioning issues
echo -n " -DLEAN_STANDALONE=ON -DCADICAL_USE_CUSTOM_CXX=ON"
echo -n " -DCMAKE_CXX_COMPILER=$PWD/llvm-host/bin/clang++ -DLEAN_CXX_STDLIB='-L ROOT/lib -Wl,-Bstatic -lc++ -lc++abi -Wl,-Bdynamic'"
echo -n " -DLEAN_EXTRA_CXX_FLAGS='--sysroot $PWD/llvm -idirafter $GLIBC_DEV/include ${EXTRA_FLAGS:-}'"
# use target compiler directly when not cross-compiling
if [[ -L llvm-host ]]; then
  echo -n " -DCMAKE_C_COMPILER=$PWD/stage1/bin/clang"
else
  echo -n " -DCMAKE_C_COMPILER=$PWD/llvm-host/bin/clang -DLEANC_OPTS='--sysroot $PWD/stage1 -resource-dir $PWD/stage1/lib/clang/15.0.1 ${EXTRA_FLAGS:-}'"
fi
# use `-nostdinc` to make sure headers are not visible by default (in particular, not to `#include_next` in the clang headers),
# but do not change sysroot so users can still link against system libs
echo -n " -DLEANC_INTERNAL_FLAGS='--sysroot ROOT -nostdinc -isystem ROOT/include/clang' -DLEANC_CC=ROOT/bin/clang"
# Do NOT set sysroot here so glibc and crt system libs are found. `-L` still takes priority.
echo -n " -DLEANC_INTERNAL_LINKER_FLAGS='-L ROOT/lib -Wl,--as-needed -Wl,-Bstatic -lgmp -lunwind -luv -Wl,-Bdynamic -Wl,--no-as-needed -fuse-ld=lld'"
# when not using the above flags, link GMP dynamically/as usual
echo -n " -DLEAN_EXTRA_LINKER_FLAGS='-Wl,--as-needed -lgmp -luv -lpthread -ldl -lrt -Wl,--no-as-needed'"
# do not set `LEAN_CC` for tests
echo -n " -DLEAN_TEST_VARS=''"
