#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

# Test that failed imports show the module that imported them
# https://github.com/leanprover/lake/issues/25
# https://github.com/leanprover/lean4/issues/2569
# https://github.com/leanprover/lean4/issues/2415

($LAKE build +X 2>&1 && exit 1 || true) | grep -F "X.lean"
($LAKE print-paths Lib.B 2>&1 && exit 1 || true) | grep -F "Lib.B"
