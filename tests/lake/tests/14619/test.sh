#!/usr/bin/env bash
source ../common.sh
./clean.sh

# This test covers issue 14619
# https://github.com/leanprover/lean4/issues/14619

# A `lean_lib` whose root module has no source file should summarize the
# collection failure and report the missing file.
test_err "A: some modules have bad imports or could not be read" build
match_text "A.lean" produced.out

# Cleanup
rm -f produced.out
