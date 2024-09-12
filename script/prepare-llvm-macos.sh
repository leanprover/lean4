#!/usr/bin/env bash
set -uxo pipefail

# run from root build directory as in
# ```
# eval cmake ../.. $(../../script/prepare-llvm-macos.sh)
# ```

# use full LLVM release for compiling C++ code, but subset for compiling C code and distribution

GMP=${GMP:-$(brew --prefix)}
LIBUV=${LIBUV:-$(brew --prefix)}

[[ -d llvm ]] || (mkdir llvm; gtar xf $1 --strip-components 1 --directory llvm)
[[ -d llvm-host ]] || if [[ "$#" -gt 1 ]]; then
  (mkdir llvm-host; gtar xf $2 --strip-components 1 --directory llvm-host)
else
  ln -s llvm llvm-host
fi
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
# libSystem stub, includes libc
cp $SDK/usr/lib/libSystem.tbd stage1/lib/libc
# use for linking, use system lib for running
gcp llvm/lib/libc++.dylib stage1/lib/libc
# make sure we search for the library in /usr/lib instead of the rpath, which should not contain `/usr/lib`
# and apparently since Sonoma does not do so implicitly either
install_name_tool -id /usr/lib/libc++.dylib stage1/lib/libc/libc++.dylib
echo -n " -DLEAN_STANDALONE=ON"
# do not change C++ compiler; libc++ etc. being system libraries means there's no danger of conflicts,
# and the custom clang++ outputs a myriad of warnings when consuming the SDK
echo -n " -DLEAN_EXTRA_CXX_FLAGS='${EXTRA_FLAGS:-}'"
if [[ -L llvm-host ]]; then
  echo -n " -DCMAKE_C_COMPILER=$PWD/stage1/bin/clang"
  gcp $GMP/lib/libgmp.a stage1/lib/
  gcp $LIBUV/lib/libuv.a stage1/lib/
  echo -n " -DLEANC_INTERNAL_LINKER_FLAGS='-L ROOT/lib -L ROOT/lib/libc -fuse-ld=lld'"
  echo -n " -DLEAN_EXTRA_LINKER_FLAGS='-lgmp -luv'"
else
  echo -n " -DCMAKE_C_COMPILER=$PWD/llvm-host/bin/clang -DLEANC_OPTS='--sysroot $PWD/stage1 -resource-dir $PWD/stage1/lib/clang/15.0.1 ${EXTRA_FLAGS:-}'"
  echo -n " -DLEANC_INTERNAL_LINKER_FLAGS='-L ROOT/lib -L ROOT/lib/libc -fuse-ld=lld'"
fi
echo -n " -DLEANC_INTERNAL_FLAGS='-nostdinc -isystem ROOT/include/clang' -DLEANC_CC=ROOT/bin/clang"
# do not set `LEAN_CC` for tests
echo -n " -DLEAN_TEST_VARS=''"
