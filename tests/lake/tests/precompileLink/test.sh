#!/usr/bin/env bash
source ../common.sh

./clean.sh

PKG=precompileArgs

# Test that precompilation works with a Lake import
# https://github.com/leanprover/lean4/issues/7388
test_run -v build LakeTest

# Test that the link & load order of precompiled libraries is correct
# https://github.com/leanprover/lean4/issues/7790
test_run -v exe orderTest

# Test that transitively importing a precompiled module
# from a non-precompiled module works
test_not_out '"plugins":[]' -v setup-file ImportDownstream.lean
test_run -v build Downstream

# Test that a library with `precompileLibrary` is precompiled for the modules
# that import it, but not for its own modules
test_run -v build Lib
test_exp ! -f .lake/build/lib/lean/${PKG}_Lib_Base.$SHARED_LIB_EXT
test_exp ! -f .lake/build/lib/${LIB_PREFIX}${PKG}_Lib.$SHARED_LIB_EXT
test_exp ! -f .lake/build/lib/${LIB_PREFIX}${PKG}_LibDep.$SHARED_LIB_EXT
test_out '"plugins":[]' -v setup-file Lib.lean
test_out '"dynlibs":[]' -v setup-file Lib.lean
test_run -v build LibDownstream
test_exp -f .lake/build/lib/${LIB_PREFIX}${PKG}_Lib.$SHARED_LIB_EXT
test_not_out '"plugins":[]' -v setup-file LibDownstream.lean

# Test that `moreLinkArgs` are included when linking precompiled modules
./clean.sh
test_maybe_err "-lBogus" build -KlinkArgs=-lBogus
./clean.sh

# Test that dynlibs are part of the module trace unless `platformIndependent` is set
test_run build -R
echo foo > .lake/build/lib/lean/${PKG}_Foo_Bar.$SHARED_LIB_EXT
test_err "Building Foo" build --rehash
test_cmd rm -f .lake/build/lib/lean/${PKG}_Foo_Bar.$SHARED_LIB_EXT
test_run build -R -KplatformIndependent=true
echo foo > .lake/build/lib/lean/${PKG}_Foo_Bar.$SHARED_LIB_EXT
test_run build --rehash --no-build

# Test that `platformIndependent` can be toggled without a rebuild
# if the library does not depend on any dynamic libraries
test_run build -R +PlatformIndependent
test_run build -R -KplatformIndependent=true +PlatformIndependent --no-build
test_run build -R +PlatformIndependent --no-build

# cleanup
rm -f produced.out
