#!/usr/bin/env bash
source ../common.sh

./clean.sh

# https://github.com/leanprover/lean4/issues/10825
# When Lean already printed errors and exited with code 1, Lake should not
# add the redundant "Lean exited with code 1" line.

echo "# TEST: elide exit-code noise on ordinary type errors"
lake_out build TypeError || true
match_text "Type mismatch" produced.outno_match_text "Lean exited with code 1" produced.out
# Build should still fail
test_fails build TypeError

echo "# TEST: keep exit-code message for non-1 exit codes"
lake_out build Exit3 || true
match_text "Lean exited with code 3" produced.out

# Cleanup
rm -f produced.out
