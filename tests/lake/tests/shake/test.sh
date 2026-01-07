#!/usr/bin/env bash
source ../common.sh

./clean.sh

TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"

# Test the `lake shake` command

# Copy input project to working directory
cp -r input/* .

# Build the project first (shake needs .olean files)
test_run build

# Run shake to check for unused imports (using --force to skip the lake build --no-build check)
# Shake exits with code 1 when issues are found, which is expected here
lake_out shake --force Main || true
match_pat 'remove.*Lib.B' produced.out
