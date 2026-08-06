#!/usr/bin/env bash
source ../common.sh

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

echo "# TEST: a header change rebuilds the object file"
echo "// touched" >> $INCLUDE_DIR/lean/lean.h
test_status $NO_BUILD_CODE build +Test:c.o.export --no-build
test_err "Building Test:c.o" build +Test:c.o.export --no-build
test_run build +Test:c.o.export
test_out "All targets up-to-date" build +Test:c.o.export --no-build

# Cleanup
rm -f produced.out
