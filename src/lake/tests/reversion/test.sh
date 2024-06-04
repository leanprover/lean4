#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that introducing an error and reverting works
# https://github.com/leanprover/lean4/issues/4303

echo 'def hello := "foo"' > Hello.lean
$LAKE -q build | diff - /dev/null
echo 'error' > Hello.lean
$LAKE build && exit 1 || true
echo 'def hello := "foo"' > Hello.lean
$LAKE -q build | diff - /dev/null
