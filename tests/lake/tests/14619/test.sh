#!/usr/bin/env bash
source ../common.sh
./clean.sh

# This test covers issue 14619
# https://github.com/leanprover/lean4/issues/14619

# A `lean_lib` whose root module has no source file should report the missing
# file, not just "some modules have bad imports".
test_err "A.lean" build

# Cleanup
rm -f produced.out
