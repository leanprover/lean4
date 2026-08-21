#!/usr/bin/env bash
# Authors: Sebastian Ullrich, Mac Malone, Claude Code
source ../../tests/common.sh

# A `bootstrap` package compiles its C files against the Lean headers in its own build
# directory rather than the toolchain's, so the toolchain githash does not identify them.
# Tests that Lake traces those headers instead.

./clean.sh

NO_BUILD_CODE=3
INCLUDE_DIR=.lake/build/include

test_cmd mkdir -p $INCLUDE_DIR
test_cmd cp -r "$(norm_path "$(lean --print-prefix)")/include/lean" $INCLUDE_DIR/

test_run build +Test:c.o.export
test_out "All targets up-to-date" build +Test:c.o.export --no-build

# The C files `lean` emits include only `lean.h`, which pulls in the rest transitively
for header in lean.h config.h version.h mimalloc.h; do
  echo "# TEST: a change to $header rebuilds the object file"
  echo "// touched" >> $INCLUDE_DIR/lean/$header
  test_status $NO_BUILD_CODE build +Test:c.o.export --no-build
  test_err "Building Test:c.o" build +Test:c.o.export --no-build
  test_run build +Test:c.o.export
  test_out "All targets up-to-date" build +Test:c.o.export --no-build
done

# `USE_MIMALLOC` controls both whether `mimalloc.h` is in the include directory
# and whether `config.h` defines the `LEAN_MIMALLOC` that makes `lean.h` include it
echo "# TEST: an absent optional header does not fail the build"
test_cmd rm $INCLUDE_DIR/lean/mimalloc.h
sed_i "/define LEAN_MIMALLOC/d" $INCLUDE_DIR/lean/config.h
test_run build +Test:c.o.export
test_out "All targets up-to-date" build +Test:c.o.export --no-build

# Cleanup
rm -f produced.out
