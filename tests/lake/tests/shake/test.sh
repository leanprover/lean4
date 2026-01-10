#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the `lake shake` command

# Copy input project to working directory
cp -r input/* .

# Build the project first (shake needs .olean files)
test_run build

# Run shake to check for unused imports
# Shake exits with code 1 when issues are found, which is expected here
lake_out shake Main || true
match_pat 'remove.*Lib.B' produced.out

# Test --fix mode: apply the fixes and verify the result
./clean.sh
cp -r input/* .
test_run build
test_run shake --fix Main

# Verify Main.lean matches expected (Lib.B import removed)
check_diff expected/Main.lean Main.lean
