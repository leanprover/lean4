#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# Test the behavior of `lake fetch`
# ---

# Check that logs are not written to stdout
$LAKE fetch | diff - /dev/null

# Test that fetching an executable
# returns its path which can then be executed
`$LAKE fetch a`

# Test fetching multiple targets
test `$LAKE fetch a b | wc -l` = 2
