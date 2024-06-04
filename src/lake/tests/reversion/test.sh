#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that introducing an error and reverting works
# https://github.com/leanprover/lean4/issues/4303

# Initial state
echo 'def hello := "foo"' > Hello.lean
$LAKE -q build
# Introduce error
echo 'error' > Hello.lean
$LAKE build && exit 1 || true
# Revert
echo 'def hello := "foo"' > Hello.lean
# Ensure error is not presevered but the warning in another file is
$LAKE -q build | grep --color 'Replayed Main'
