#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that the link & load order of precompiled libraries is correct
# https://github.com/leanprover/lean4/issues/7790
test_run -v exe orderTest

# Test that `moreLinkArgs` are included when linking precompiled modules
./clean.sh
test_maybe_err "-lBogus" build -KlinkArgs=-lBogus
./clean.sh

# Test that dynlibs are part of the module trace unless `platformIndependent` is set
test_run build -R
echo foo > .lake/build/lib/lean/Foo_Bar.$SHARED_LIB_EXT
test_err "Building Foo" build --rehash
rm .lake/build/lib/lean/Foo_Bar.$SHARED_LIB_EXT
test_run build -R -KplatformIndependent=true
echo foo > .lake/build/lib/lean/Foo_Bar.$SHARED_LIB_EXT
test_run build --rehash --no-build

# cleanup
rm -f produced.out
