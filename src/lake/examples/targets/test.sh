#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

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

# Test error on nonexistent facet
! $LAKE build targets:noexistent

# Test custom targets and package, library, and module facets
$LAKE build bark | grep -m1 Bark!
$LAKE build targets/bark_bark | grep -m1 Bark!
$LAKE build targets:print_name | grep -m1 targets
$LAKE build Foo.Bar:print_src | grep -m1 Bar.lean
$LAKE build foo:print_name | grep -m1 foo

# Test the module `deps` facet
$LAKE build Foo:deps
test -f ./build/lib/Foo/Bar.olean
test ! -f ./build/lib/Foo.olean

# Test the module specifier
test ! -f ./build/lib/Foo/Baz.olean
$LAKE build +Foo.Baz
test -f ./build/lib/Foo/Baz.olean

# Test `o` specifier
test ! -f ./build/ir/Bar.o
$LAKE build Bar:o
test -f ./build/ir/Bar.o

# Test default targets
test ! -f ./build/bin/c
test ! -f ./build/lib/Foo.olean
test ! -f ./build/lib/${LIB_PREFIX}Foo.a
test ! -f ./build/meow.txt
$LAKE build targets/
./build/bin/c
test -f ./build/lib/Foo.olean
test -f ./build/lib/${LIB_PREFIX}Foo.a
cat ./build/meow.txt | grep -m1 Meow!

# Test shared lib facets
test ! -f ./build/lib/${LIB_PREFIX}Foo.$SHARED_LIB_EXT
test ! -f ./build/lib/${LIB_PREFIX}Bar.$SHARED_LIB_EXT
$LAKE build foo:shared bar
test -f ./build/lib/${LIB_PREFIX}Foo.$SHARED_LIB_EXT
test -f ./build/lib/${LIB_PREFIX}Bar.$SHARED_LIB_EXT

# Test dynlib facet
test ! -f ./build/lib/${LIB_PREFIX}Foo-1.$SHARED_LIB_EXT
$LAKE build Foo:dynlib
test -f ./build/lib/${LIB_PREFIX}Foo-1.$SHARED_LIB_EXT

# Test library `extraDepTargets`
test ! -f ./build/caw.txt
test ! -f ./build/lib/Baz.olean
$LAKE build baz
test -f ./build/lib/Baz.olean
cat ./build/caw.txt | grep -m1 Caw!

# Test executable build
$LAKE build a b
./build/bin/a
./build/bin/b

# Test repeat build works
$LAKE build bark | grep -m1 Bark!
