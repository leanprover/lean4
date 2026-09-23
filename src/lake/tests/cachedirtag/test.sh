#!/usr/bin/env bash

# Test that CACHEDIR.TAG file is correctly created in .lake directory.
#
# Removing CACHEDIR.TAG without removing .lake directory and then rebuilding
# does not currently recreate CACHEDIR.TAG. This is an artifact of the current
# implementation and is technically against the spec:
#
# > The application should also regenerate the cache directory tag if it
# > disappears --

set -euxo pipefail

rm -rf hello

unamestr=`uname`
if [ "$unamestr" = Darwin ] || [ "$unamestr" = FreeBSD ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

assert_cachedir_tag() {
    test -f "$1"
    # According to spec, the first 43 bytes are fixed: https://bford.info/cachedir/
    test "`head -c43 "$1"`" = "Signature: 8a477f597d28d172789f06886806bc55"
}

LAKE=${LAKE:-../../.lake/build/bin/lake}

$LAKE new hello
test ! -e hello/.lake
# Building craetes CACHEDIR.TAG
$LAKE -d hello build
test -d hello/.lake
assert_cachedir_tag hello/.lake/CACHEDIR.TAG
# Rebuilding does not recreate CACHEDIR.TAG
rm hello/.lake/CACHEDIR.TAG
test ! -e hello/.lake/CACHEDIR.TAG
$LAKE -d hello build
test ! -e hello/.lake/CACHEDIR.TAG
# Rebuilding from scratch recreates CACHEDIR.TAG
rm -r hello/.lake
test ! -e hello/.lake
$LAKE -d hello build
assert_cachedir_tag hello/.lake/CACHEDIR.TAG
# Building by lake exe also creates CACHEDIR.TAG
rm -r hello/.lake
test ! -e hello/.lake
$LAKE -d hello exe hello
assert_cachedir_tag hello/.lake/CACHEDIR.TAG
rm -rf hello
