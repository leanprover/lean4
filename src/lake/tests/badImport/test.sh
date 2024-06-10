#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that failed imports show the module that imported them
# https://github.com/leanprover/lake/issues/25
# https://github.com/leanprover/lean4/issues/2569
# https://github.com/leanprover/lean4/issues/2415
# https://github.com/leanprover/lean4/issues/3351
# https://github.com/leanprover/lean4/issues/3809

# Test importing a nmissing module from outside the workspace
($LAKE build +X 2>&1 && exit 1 || true) | grep --color -F "X.lean:1:0: unknown package 'Y'"
$LAKE setup-file ./X.lean Y # Lake ignores the file (the server will error)
# Test importing onself
($LAKE build +Lib.A 2>&1 && exit 1 || true) | grep --color -F "A.lean: module imports itself"
($LAKE setup-file ./Lib/A.lean Lib.A 2>&1 && exit 1 || true) | grep --color -F "A.lean: module imports itself"
# Test importing a missing module from within the workspace
($LAKE build +Lib.B 2>&1 && exit 1 || true) | grep --color -F "B.lean: bad import 'Lib.Y'"
($LAKE setup-file X.lean Lib.B 2>&1 && exit 1 || true) | grep --color "B.lean: bad import 'Lib.Y'"
# Test a vanishing import within the workspace (lean4#3551)
touch Lib/Y.lean
$LAKE build +Lib.B
rm Lib/Y.lean
($LAKE build +Lib.B 2>&1 && exit 1 || true) | grep --color -F "B.lean: bad import 'Lib.Y'"
($LAKE setup-file ./X.lean Lib.B 2>&1 && exit 1 || true) | grep --color "B.lean: bad import 'Lib.Y'"
# Test a module C which imports another module A which contains a bad import
($LAKE build +Lib.C 2>&1 && exit 1 || true) | grep --color -F "C.lean: bad import 'Lib.A'"
($LAKE setup-file Lib/C.lean Lib.A 2>&1 && exit 1 || true) | grep --color -F "C.lean: bad import 'Lib.A'"

