#!/usr/bin/env bash
source ../common.sh

# Prevent MSYS2 from automatically transforming path-like targets
[ "$OSTYPE" == "cygwin" -o "$OSTYPE" == "msys" ] && export MSYS2_ARG_CONV_EXCL=*

PKG=targets

./clean.sh

# Test errors on nonexistent facets
test_err 'unknown package facet `bogus`' build targets:bogus
test_err 'unknown lean_lib facet `bogus`' build Foo:bogus
test_err 'unknown module facet `bogus`'  build +Foo:bogus
test_err 'unknown lean_exe facet `bogus`' build a:bogus

# Test custom targets and package, library, and module facets
# `diff_out` runs as the tail of a pipeline, so its expected-output argument
# must be a real file. Do not inline it via process substitution
# (e.g. `$LAKE build bark | diff_out '/Bark!/' <(cat << 'EOF' ... EOF)`): the
# resulting `/dev/fd` is not reliably inherited by the `diff` inside `diff_out`
# on macOS, which then fails with `Bad file descriptor`.
diff_out() {
  awk "/Ran/,$1" | sed '/Ran/ s/^[^R]*//' | diff -u --strip-trailing-cr $2 -
}
cat << 'EOF' > produced.expected
Ran targets/bark
info: Bark!
EOF
$LAKE build bark | diff_out '/Bark!/' produced.expected
cat << 'EOF' > produced.expected
Ran targets/bark
info: Bark!
Build completed successfully (2 jobs).
EOF
$LAKE build targets/bark_bark | diff_out '0' produced.expected
cat << 'EOF' > produced.expected
Ran targets:print_name
info: stdout/stderr:
targets
EOF
$LAKE build targets:print_name | diff_out '/^targets/' produced.expected
cat << 'EOF' > produced.expected
Ran targets/Foo:print_name
info: stdout/stderr:
Foo
EOF
$LAKE build Foo:print_name | diff_out '/^Foo/' produced.expected
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

# Cleanup
rm -f produced.out produced.expected
