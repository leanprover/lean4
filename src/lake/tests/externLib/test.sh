#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests the successful compilation of an `extern_lib`
test_run -d ffi -v exe test

# Tests the successful precompilation of an `extern_lib` (from a dep)
test_run -v build Test

# Tests the successful compilation of an `extern_lib` from a dep
test_run -v exe test

# Cleanup
rm -f produced.out
