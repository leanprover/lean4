#!/usr/bin/env bash
set -euo pipefail

# Ensure this runs from the lake test directory
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

# The tests read and write more than Lake's sandbox lets a project's code reach
export LAKE_NO_SANDBOX=1

# Build `LAKE` from this directory or use the provided one
LAKE=${LAKE:-$(lake query lake)}

# Run the test
TEST_DIR="$1"; shift
CMD1="cd \"$TEST_DIR\" && ./test.sh"
CMD2='rc=$?; echo "EXIT: $rc"; exit $rc'
$LAKE env bash -c "$CMD1; $CMD2"
