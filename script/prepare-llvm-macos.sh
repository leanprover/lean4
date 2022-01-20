#!/usr/bin/env bash
set -uxo pipefail

# run from root build directory as in
# ```
# eval cmake ../.. $(../../script/prepare-llvm-macos.sh)
# ```

# use full LLVM release for compiling C++ code, but subset for compiling C code and distribution

[[ -d llvm ]] || (mkdir llvm; gtar xf $1 --strip-components 1 --directory llvm)
SDK=$(xcrun --show-sdk-path)
mkdir -p stage1/{bin,lib/libc,include/clang}
CP="gcp -d"  # preserve symlinks
# a C compiler!
gcp -L llvm/bin/clang stage1/bin/
# a linker!
gcp -L llvm/bin/ld64.lld stage1/bin/
# a static archiver!
gcp -L llvm/bin/llvm-ar stage1/bin/
# dependencies of the above
$CP llvm/lib/lib{clang-cpp,LLVM}.dylib stage1/lib/
#find stage1 -type f -exec strip --strip-unneeded '{}' \; 2> /dev/null
# lean.h dependencies
$CP llvm/lib/clang/*/include/{std*,__std*,limits}.h stage1/include/clang
# runtime
(cd llvm; $CP --parents lib/clang/*/lib/*/libclang_rt.osx.a ../stage1)
gcp ${GMP:-/usr/local/opt/gmp}/lib/libgmp.a stage1/lib/
# libSystem stub, includes libc
cp $SDK/usr/lib/libSystem.tbd stage1/lib/libc
# use for linking, use system libs for running
gcp llvm/lib/lib{c++,c++abi,unwind}.dylib stage1/lib/libc
echo -n " -DLEAN_STANDALONE=ON"
# do not change C++ compiler; libc++ etc. being system libraries means there's no danger of conflicts,
# and the custom clang++ outputs a myriad of warnings when consuming the SDK
echo -n " -DCMAKE_C_COMPILER=$PWD/stage1/bin/clang"
echo -n " -DGMP_LIBRARIES=lib/libgmp.a -DGMP_INCLUDE_DIR=/usr/local/opt/gmp/include"
echo -n " -DLEANC_INTERNAL_FLAGS='-nostdinc -isystem ROOT/include/clang' -DLEANC_CC=ROOT/bin/clang"
echo -n " -DLEANC_INTERNAL_LINKER_FLAGS='-L ROOT/lib -L ROOT/lib/libc -fuse-ld=lld'"
# do not set `LEAN_CC` for tests
echo -n " -DLEAN_TEST_VARS=''"
