#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests the successful compilation of an `extern_lib`
test_run -d ffi -v exe test

# Tests the successful precompilation of an `extern_lib` (from a dep)
test_run -v build Test

# Tests the successful compilation of an `extern_lib` from a dep
test_run -v exe test

# Tests that a non-precompiled build does not load anything as a dynlib/plugin
# https://github.com/leanprover/lean4/issues/4565
test_not_pat 'load-dynlib|plugin' -v build test
test_not_pat 'load-dynlib|plugin' -v -d ffi build test

# Cleanup
rm -f produced.out
