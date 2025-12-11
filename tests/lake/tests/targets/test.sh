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

PKG=targets

./clean.sh

# Test error on nonexistent facet
$LAKE build targets:noexistent && exit 1 || true

# Test custom targets and package, library, and module facets
diff_out() {
  awk "/Ran/,$1" | sed '/Ran/ s/^[^R]*//' | diff -u --strip-trailing-cr $2 -
}
$LAKE build bark | diff_out '/Bark!/' <(cat << 'EOF'
Ran targets/bark
info: Bark!
EOF
)
$LAKE build targets/bark_bark | diff_out '0' <(cat << 'EOF'
Ran targets/bark
info: Bark!
Build completed successfully (2 jobs).
EOF
)
$LAKE build targets:print_name | diff_out '/^targets/' <(cat << 'EOF'
Ran targets:print_name
info: stdout/stderr:
targets
EOF
)
$LAKE build Foo:print_name | diff_out '/^Foo/' <(cat << 'EOF'
Ran targets/Foo:print_name
info: stdout/stderr:
Foo
EOF
)
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
test ! -f ./.lake/build/lib/${LIB_PREFIX}${PKG}_Foo.a
test ! -f ./.lake/build/meow.txt
$LAKE build targets/
./.lake/build/bin/c
test -f ./.lake/build/lib/lean/Foo.olean
test -f ./.lake/build/lib/${LIB_PREFIX}${PKG}_Foo.a
cat ./.lake/build/meow.txt | grep Meow!

# Test shared lib facets
test ! -f ./.lake/build/lib/${LIB_PREFIX}${PKG}_Foo.$SHARED_LIB_EXT
test ! -f ./.lake/build/lib/libBar.$SHARED_LIB_EXT
$LAKE build Foo:shared Bar
test -f ./.lake/build/lib/${LIB_PREFIX}${PKG}_Foo.$SHARED_LIB_EXT
test -f ./.lake/build/lib/libBar.$SHARED_LIB_EXT

# Test static lib facet
test ! -f ./.lake/build/lib/libBar.a
$LAKE build Foo:shared Bar:static
test -f ./.lake/build/lib/libBar.a

# Test dynlib facet
test ! -f ./.lake/build/lib/lean/${PKG}_Foo.$SHARED_LIB_EXT
$LAKE build +Foo:dynlib
test -f ./.lake/build/lib/lean/${PKG}_Foo.$SHARED_LIB_EXT

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

# Test build by module path
rm -f .lake/build/bin/a
rm -f .lake/build/lib/lean/a.olean
rm -f .lake/build/lib/lean/Foo/Baz.olean
rm -f  .lake/build/ir/Bar.c.o.export
$LAKE build -v src/Foo/Baz.lean src/Bar.lean:c.o.export
test -f .lake/build/lib/lean/Foo/Baz.olean
test -f .lake/build/ir/Bar.c.o.export
$LAKE build -v src/a.lean
test -f .lake/build/lib/lean/a.olean
test ! -f .lake/build/bin/a
