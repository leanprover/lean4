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

# Test a module with a bad import does not kill the whole build
($LAKE build Lib.U Etc 2>&1 && exit 1 || true) | grep --color -F "Building Etc"
# Test importing a nmissing module from outside the workspace
($LAKE build +Lib.U 2>&1 && exit 1 || true) | grep --color -F "U.lean:2:0: unknown module prefix 'Bogus'"
$LAKE setup-file . Bogus # Lake ignores the file (the server will error)
# Test importing onself
($LAKE build +Lib.S 2>&1 && exit 1 || true) | grep --color -F "S.lean: module imports itself"
($LAKE setup-file ./Lib/S.lean Lib.S 2>&1 && exit 1 || true) | grep --color -F "S.lean: module imports itself"
# Test importing a missing module from within the workspace
($LAKE build +Lib.B 2>&1 && exit 1 || true) | grep --color -F "B.lean: bad import 'Lib.Bogus'"
($LAKE setup-file ./Lib/B.lean Lib.Bogus 2>&1 && exit 1 || true) | grep --color "B.lean: bad import 'Lib.Bogus'"
# Test a vanishing import within the workspace (lean4#3551)
touch Lib/Bogus.lean
$LAKE build +Lib.B
rm Lib/Bogus.lean
($LAKE build +Lib.B 2>&1 && exit 1 || true) | grep --color -F "B.lean: bad import 'Lib.Bogus'"
($LAKE setup-file . Lib.B 2>&1 && exit 1 || true) | grep --color "B.lean: bad import 'Lib.Bogus'"
# Test a module which imports a module containing a bad import
($LAKE build +Lib.B1 2>&1 && exit 1 || true) | grep --color -F "B1.lean: bad import 'Lib.B'"
($LAKE setup-file ./Lib/B1.lean Lib.B 2>&1 && exit 1 || true) | grep --color -F "B1.lean: bad import 'Lib.B'"
# Test an executable with a bad import does not kill the whole build
($LAKE build X Etc 2>&1 && exit 1 || true) | grep --color -F "Building Etc"
# Test an executable which imports a missing module from within the workspace
($LAKE build X 2>&1 && exit 1 || true) | grep --color -F "X.lean: bad import 'Lib.Bogus'"
# Test a executable which imports a module containing a bad import
($LAKE build X1 2>&1 && exit 1 || true) | grep --color -F "B.lean: bad import 'Lib.Bogus'"
