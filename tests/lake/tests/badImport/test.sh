#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that failed imports show the module that imported them
# https://github.com/leanprover/lake/issues/25
# https://github.com/leanprover/lean4/issues/2569
# https://github.com/leanprover/lean4/issues/2415
# https://github.com/leanprover/lean4/issues/3351
# https://github.com/leanprover/lean4/issues/3809

# Test a module with a bad import does not kill the whole build
test_err "Building Etc" build Lib.U Etc
# Test importing a missing module from outside the workspace
test_err "U.lean:2:0: unknown module prefix 'Bogus'" build +Lib.U
test_err "U.lean:2:0: error: unknown module prefix 'Bogus'" lean ./Lib/U.lean
test_run setup-file ./Lib/U.lean # Lake ignores the unknown import (the server will error)
# Test importing oneself
test_err "S.lean: module imports itself" build +Lib.S
test_err "S.lean: module imports itself" lean ./Lib/S.lean
test_err "S.lean: module imports itself" setup-file ./Lib/S.lean
# Test importing a missing module from within the workspace
test_err "B.lean: bad import 'Lib.Bogus'" build +Lib.B
test_err "B.lean: bad import 'Lib.Bogus'" lean ./Lib/B.lean
test_err "B.lean: bad import 'Lib.Bogus'" setup-file ./Lib/B.lean
# Test a vanishing import within the workspace (lean4#3551)
echo "# TEST: Vanishing Import"
test_cmd touch Lib/Bogus.lean
test_run build +Lib.B
test_cmd rm Lib/Bogus.lean
test_err "B.lean: bad import 'Lib.Bogus'" build +Lib.B
test_err "B.lean: bad import 'Lib.Bogus'" lean ./Lib/B.lean
test_err "B.lean: bad import 'Lib.Bogus'" setup-file ./Lib/B.lean
# Test a module which imports a module containing a bad import
test_err "B1.lean: bad import 'Lib.B'" build +Lib.B1
test_err "B1.lean: bad import 'Lib.B'" lean ./Lib/B1.lean
test_err "B1.lean: bad import 'Lib.B'" setup-file ./Lib/B1.lean
# Test an executable with a bad import does not kill the whole build
test_err "Building Etc" build X Etc
# Test an executable which imports a missing module from within the workspace
test_err "X.lean: bad import 'Lib.Bogus'" build X
# Test an executable which imports a module containing a bad import
test_err "B.lean: bad import 'Lib.Bogus'" build X1

# Cleanup
rm -f produced.out
