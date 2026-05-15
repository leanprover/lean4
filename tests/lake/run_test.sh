#!/usr/bin/env bash
set -euo pipefail

# Ensure this runs from the lake test directory
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

# Build `LAKE` from this directory or use the provided one
LAKE=${LAKE:-$(lake query lake)}

# Run the test
TEST_DIR="$1"; shift
cd "$TEST_DIR"
$LAKE env bash test.sh
