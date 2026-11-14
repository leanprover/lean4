#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests that Lake errors if a module's source file changes during its build
# rather than saving a trace that pairs the old source with the new outputs.

# The build rewrites `Foo.lean`, so work on a copy
copy_to_work lakefile.toml Foo.lean

echo "# TEST: source changed during build"
LAKE_TEST_TOUCH=1 test_err "changed since build began" build
test_exp ! -f .lake/build/lib/lean/Foo.trace

echo "# TEST: rerun succeeds"
test_run build
test_exp -f .lake/build/lib/lean/Foo.trace

# Cleanup
rm -f produced.out
