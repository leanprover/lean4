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
$CP $(grealpath llvm/bin/clang) stage1/bin/clang
# a linker!
gcp llvm/bin/ld64.lld stage1/bin/
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
echo -n " -DCMAKE_C_COMPILER=$PWD/stage1/bin/clang -DCMAKE_CXX_COMPILER=$PWD/llvm/bin/clang++"
# allow C++ code to include /usr since it needs quite a few more headers
# need no-macro-redefined for weird clang stdint.h
echo -n " -DLEAN_EXTRA_CXX_FLAGS='--sysroot $PWD/llvm --stdlib=libc++ -I $SDK/usr/include -Wno-macro-redefined'"
echo -n " -DGMP_LIBRARIES=lib/libgmp.a -DGMP_INCLUDE_DIR=/usr/local/opt/gmp/include"
echo -n " -DLEANC_INTERNAL_FLAGS='--sysroot ROOT -I ROOT/include/clang -Wno-macro-redefined' -DLEANC_CC=ROOT/bin/clang"
echo -n " -DLEANC_INTERNAL_LINKER_FLAGS='-L ROOT/lib -L ROOT/lib/libc -fuse-ld=lld'"
# do not set `LEAN_CC` for tests
echo -n " -DLEAN_TEST_VARS=''"
