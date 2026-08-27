#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the `lake shake` command

# `shake --fix` rewrites the sources it is given, so work on a copy
copy_to_work input/*

# Build the project first (shake needs .olean files)
test_run build

# Run shake to check for unused imports
# Shake exits with code 1 when issues are found, which is expected here
lake_out shake Main || true
match_pat 'remove.*Lib.B' produced.out

# This should succeed
lake_out shake --only DepMain

# Test --fix mode: apply the fixes and verify the result
cd ..
./clean.sh
copy_to_work input/*
test_run build
test_run shake --fix Main
test_run build

# Verify Main.lean matches expected
check_diff ../expected/Main.lean Main.lean
