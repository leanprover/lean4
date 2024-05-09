#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that failed imports show the module that imported them
# https://github.com/leanprover/lake/issues/25
# https://github.com/leanprover/lean4/issues/2569
# https://github.com/leanprover/lean4/issues/2415
# https://github.com/leanprover/lean4/issues/3809

($LAKE build +X 2>&1 && exit 1 || true) | grep --color -F "X.lean"
($LAKE build +Lib.A 2>&1 && exit 1 || true) | grep --color -F "build cycle"
($LAKE setup-file ./Lib/A.lean Lib.A 2>&1 && exit 1 || true) | grep --color -F "build cycle"
($LAKE build +Lib.B 2>&1 && exit 1 || true) | grep --color -F "B.lean"
($LAKE setup-file ./X.lean Lib.B 2>&1 && exit 1 || true) | grep --color -F "B.lean"
