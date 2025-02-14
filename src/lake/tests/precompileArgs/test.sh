#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

if [ "$OS" = Windows_NT ]; then
LIB_PREFIX=
SHARED_LIB_EXT=dll
elif [ "`uname`" = Darwin ]; then
LIB_PREFIX=lib
SHARED_LIB_EXT=dylib
else
LIB_PREFIX=lib
SHARED_LIB_EXT=so
fi

./clean.sh

# Test that `moreLinkArgs` are included when linking precompiled modules
($LAKE build -KlinkArgs=-lBaz 2>&1 || true) | grep --color -- "-lBaz"

# Test that dynlibs are part of the module trace unless `platformIndependent` is set
$LAKE build -R
echo foo > .lake/build/lib/lean/Foo_Bar.$SHARED_LIB_EXT
($LAKE build 2>&1 --rehash && exit 1 || true) | grep --color "Building Foo"
rm .lake/build/lib/lean/Foo_Bar.$SHARED_LIB_EXT
$LAKE build -R -KplatformIndependent=true
echo foo > .lake/build/lib/lean/Foo_Bar.$SHARED_LIB_EXT
$LAKE build --rehash --no-build
