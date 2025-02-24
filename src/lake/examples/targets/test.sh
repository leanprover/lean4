#!/usr/bin/env bash
set -exo pipefail

# Prevent MSYS2 from automatically transforming path-like targets
[ "$OSTYPE" == "cygwin" -o "$OSTYPE" == "msys" ] && export MSYS2_ARG_CONV_EXCL=*

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
$LAKE build targets:noexistent && exit 1 || true

# Test custom targets and package, library, and module facets
$LAKE build bark | awk '/Ran/,/Bark!/' | diff -u --strip-trailing-cr <(cat << 'EOF'
ℹ [1/1] Ran targets/bark
info: Bark!
EOF
) -
$LAKE build targets/bark_bark | awk '/Ran/,0' | diff -u --strip-trailing-cr <(cat << 'EOF'
ℹ [1/2] Ran targets/bark
info: Bark!
Build completed successfully.
EOF
) -
$LAKE build targets:print_name | awk '/Ran/,/^targets/' | diff -u --strip-trailing-cr <(cat << 'EOF'
ℹ [1/1] Ran targets:print_name
info: stdout/stderr:
targets
EOF
) -
$LAKE build Foo:print_name | awk '/Ran/,/^Foo/' | diff -u --strip-trailing-cr <(cat << 'EOF'
ℹ [1/1] Ran targets/Foo:print_name
info: stdout/stderr:
Foo
EOF
) -
$LAKE build Foo.Bar:print_src | grep --color Bar.lean

# Test the module `deps` facet
$LAKE build +Foo:deps
test -f ./.lake/build/lib/lean/Foo/Bar.olean
test ! -f ./.lake/build/lib/lean/Foo.olean

# Test the module specifier
test ! -f ./.lake/build/lib/lean/Foo/Baz.olean
$LAKE build +Foo.Baz
test -f ./.lake/build/lib/lean/Foo/Baz.olean

# Test an object file specifier
test ! -f ./.lake/build/ir/Bar.c.o.export
$LAKE build +Bar:c.o.export
test -f ./.lake/build/ir/Bar.c.o.export

# Test default targets
test ! -f ./.lake/build/bin/c
test ! -f ./.lake/build/lib/lean/Foo.olean
test ! -f ./.lake/build/lib/${LIB_PREFIX}Foo.a
test ! -f ./.lake/build/meow.txt
$LAKE build targets/
./.lake/build/bin/c
test -f ./.lake/build/lib/lean/Foo.olean
test -f ./.lake/build/lib/${LIB_PREFIX}Foo.a
cat ./.lake/build/meow.txt | grep Meow!

# Test shared lib facets
test ! -f ./.lake/build/lib/${LIB_PREFIX}Foo.$SHARED_LIB_EXT
test ! -f ./.lake/build/lib/${LIB_PREFIX}Bar.$SHARED_LIB_EXT
$LAKE build Foo:shared Bar
test -f ./.lake/build/lib/${LIB_PREFIX}Foo.$SHARED_LIB_EXT
test -f ./.lake/build/lib/${LIB_PREFIX}Bar.$SHARED_LIB_EXT

# Test dynlib facet
test ! -f ./.lake/build/lib/lean/Foo.$SHARED_LIB_EXT
$LAKE build +Foo:dynlib
test -f ./.lake/build/lib/lean/Foo.$SHARED_LIB_EXT

# Test library `extraDepTargets`
test ! -f ./.lake/build/caw.txt
test ! -f ./.lake/build/lib/lean/Baz.olean
$LAKE build Baz
test -f ./.lake/build/lib/lean/Baz.olean
cat ./.lake/build/caw.txt | grep Caw!

# Test executable build
$LAKE build a b
./.lake/build/bin/a
./.lake/build/bin/b
$LAKE exe @targets/a
$LAKE exe targets/a
$LAKE exe /b
$LAKE exe b

# Test repeat build works
$LAKE build bark | grep Bark!
