#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test 1: --summary with a successful build
echo "# TEST: --summary successful build"
test_out "1 job succeeded" build Good --summary

# Test 2: --summary with an up-to-date build (replays shouldn't count as "succeeded")
echo "# TEST: --summary up-to-date build"
test_out "All targets up-to-date" build Good --no-build --summary

./clean.sh

# Test 3: --summary with a failing module
echo "# TEST: --summary with failure"
test_err "1 job failed" build A B C --summary

./clean.sh
