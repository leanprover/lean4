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
test -f ./.lake/build/lib/Foo/Bar.olean
test ! -f ./.lake/build/lib/Foo.olean

# Test the module specifier
test ! -f ./.lake/build/lib/Foo/Baz.olean
$LAKE build +Foo.Baz
test -f ./.lake/build/lib/Foo/Baz.olean

# Test `.c.o` specifier
test ! -f ./.lake/build/ir/Bar.c.o
$LAKE build Bar:o
test -f ./.lake/build/ir/Bar.c.o

# Test default targets
test ! -f ./.lake/build/bin/c
test ! -f ./.lake/build/lib/Foo.olean
test ! -f ./.lake/build/lib/${LIB_PREFIX}Foo.a
test ! -f ./.lake/build/meow.txt
$LAKE build targets/
./.lake/build/bin/c
test -f ./.lake/build/lib/Foo.olean
test -f ./.lake/build/lib/${LIB_PREFIX}Foo.a
cat ./.lake/build/meow.txt | grep -m1 Meow!

# Test shared lib facets
test ! -f ./.lake/build/lib/${LIB_PREFIX}Foo.$SHARED_LIB_EXT
test ! -f ./.lake/build/lib/${LIB_PREFIX}Bar.$SHARED_LIB_EXT
$LAKE build foo:shared bar
test -f ./.lake/build/lib/${LIB_PREFIX}Foo.$SHARED_LIB_EXT
test -f ./.lake/build/lib/${LIB_PREFIX}Bar.$SHARED_LIB_EXT

# Test dynlib facet
test ! -f ./.lake/build/lib/${LIB_PREFIX}Foo-1.$SHARED_LIB_EXT
$LAKE build Foo:dynlib
test -f ./.lake/build/lib/${LIB_PREFIX}Foo-1.$SHARED_LIB_EXT

# Test library `extraDepTargets`
test ! -f ./.lake/build/caw.txt
test ! -f ./.lake/build/lib/Baz.olean
$LAKE build baz
test -f ./.lake/build/lib/Baz.olean
cat ./.lake/build/caw.txt | grep -m1 Caw!

# Test executable build
$LAKE build a b
./.lake/build/bin/a
./.lake/build/bin/b

# Test repeat build works
$LAKE build bark | grep -m1 Bark!
