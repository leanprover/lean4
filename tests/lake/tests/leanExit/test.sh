#!/usr/bin/env bash
source ../common.sh

./clean.sh

# https://github.com/leanprover/lean4/issues/10825
# Lake elides exit code 1 only when Lean already emitted error diagnostics.
# Every other exit/diagnostic combination keeps an explicit exit-code message.

echo "# TEST: elide exit code 1 after diagnostics"
lake_out build TypeError || true
match_text "Type mismatch" produced.out
no_match_text "Lean exited with code 1" produced.out
test_fails build TypeError

echo "# TEST: report exit code 1 without diagnostics"
lake_out build Exit1NoError || true
match_text "error: Lean exited with code 1" produced.out
no_match_text "Type mismatch" produced.out
test_fails build Exit1NoError

echo "# TEST: report exit code 0 when diagnostics were emitted"
lake_out build ErrorExit0 || true
match_text "Type mismatch" produced.out
match_text "error: Lean exited with code 0" produced.out
test_fails build ErrorExit0

echo "# TEST: report non-1 exit codes"
lake_out build Exit3 || true
match_text "error: Lean exited with code 3" produced.out
test_fails build Exit3

rm -f produced.out
