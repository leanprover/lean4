#!/usr/bin/env bash
source ../common.sh

./clean.sh


# Test that precompilation works with a Lake import
# https://github.com/leanprover/lean4/issues/7388
test_run -v build LakeTest

# Test that the link & load order of precompiled libraries is correct
# https://github.com/leanprover/lean4/issues/7790
test_run -v exe orderTest

# Test that transitively importing a precompiled module
# from a non-precompiled module works
test_not_out '"pluginPaths":[]' -v setup-file ImportDownstream.lean
test_run -v build Downstream

# Test that `moreLinkArgs` are included when linking precompiled modules
./clean.sh
test_maybe_err "-lBogus" build -KlinkArgs=-lBogus
./clean.sh

# Test that dynlibs are part of the module trace unless `platformIndependent` is set
PKG=precompileArgs
test_run build -R
echo foo > .lake/build/lib/lean/${PKG}_Foo_Bar.$SHARED_LIB_EXT
test_err "Building Foo" build --rehash
test_cmd rm .lake/build/lib/lean/${PKG}_Foo_Bar.$SHARED_LIB_EXT
test_run build -R -KplatformIndependent=true
echo foo > .lake/build/lib/lean/${PKG}_Foo_Bar.$SHARED_LIB_EXT
test_run build --rehash --no-build

# cleanup
rm -f produced.out
