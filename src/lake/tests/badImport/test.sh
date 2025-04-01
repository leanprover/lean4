#!/usr/bin/env bash
set -euo pipefail

exit 0  # TODO: flaky test disabled

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that failed imports show the module that imported them
# https://github.com/leanprover/lake/issues/25
# https://github.com/leanprover/lean4/issues/2569
# https://github.com/leanprover/lean4/issues/2415
# https://github.com/leanprover/lean4/issues/3351
# https://github.com/leanprover/lean4/issues/3809

test_run() {
  echo "[Command]"
  echo "$> lake" "$@"
  if $LAKE "$@" >produced.out 2>&1; then
    rc=$?
  else
    rc=$?
  fi
  echo "Lake exited with code $rc"
  echo "[Output]"
  cat produced.out
  return $rc
}

test_err() {
  expected=$1; shift
  if test_run "$@"; then rc=$?; else rc=$?; fi
  echo "[Match \"$expected\"]"
  if grep --color -F "$expected" produced.out; then
    if [ $rc != 1 ]; then
      echo "[Outcome]"
      echo "Lake unexpectedly succeeded."
      return 1
    fi
  else
    echo "No match found."
    return 1
  fi
}

# Test a module with a bad import does not kill the whole build
test_err "Building Etc" build Lib.U Etc
# Test importing a missing module from outside the workspace
test_err "U.lean:2:0: unknown module prefix 'Bogus'" build +Lib.U
test_run setup-file . Bogus # Lake ignores the file (the server will error)
# Test importing onself
test_err "S.lean: module imports itself" build +Lib.S
test_err "S.lean: module imports itself" setup-file ./Lib/S.lean Lib.S
# Test importing a missing module from within the workspace
test_err "B.lean: bad import 'Lib.Bogus'" build +Lib.B
test_err "B.lean: bad import 'Lib.Bogus'" setup-file ./Lib/B.lean Lib.Bogus
# Test a vanishing import within the workspace (lean4#3551)
echo "[Test: Vanishing Import]"
set -x
touch Lib/Bogus.lean
$LAKE build +Lib.B
rm Lib/Bogus.lean
set +x
test_err "B.lean: bad import 'Lib.Bogus'" build +Lib.B
test_err "B.lean: bad import 'Lib.Bogus'" setup-file . Lib.B
# Test a module which imports a module containing a bad import
test_err "B1.lean: bad import 'Lib.B'" build +Lib.B1
test_err "B1.lean: bad import 'Lib.B'" setup-file ./Lib/B1.lean Lib.B
# Test an executable with a bad import does not kill the whole build
test_err "Building Etc" build X Etc
# Test an executable which imports a missing module from within the workspace
test_err "X.lean: bad import 'Lib.Bogus'" build X
# Test an executable which imports a module containing a bad import
test_err "B.lean: bad import 'Lib.Bogus'" build X1

# cleanup
rm -f produced.out
