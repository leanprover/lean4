#!/usr/bin/env bash
source ../common.sh

SCRIPT="$(cd "$(dirname "$0")/../../../../script" && pwd)/count-blocked-by-build-error"

./clean.sh

# Successful build: no dependents report, exit 0.
echo "# TEST: count-blocked on a successful build"
if "$SCRIPT" --lib A --lib B --lib C --lib Good -- Good > produced.out 2>&1; then
  rc=0
else
  rc=$?
fi
cat produced.out
if [ "$rc" -ne 0 ]; then
  echo "FAILURE: expected exit 0 on successful build, got $rc"
  exit 1
fi
if grep -q "Selected-library dependents" produced.out; then
  echo "FAILURE: no dependents report expected for successful build"
  exit 1
fi

./clean.sh

# Failing build: B fails, C imports B, so B has 1 workspace dependent.
echo "# TEST: count-blocked on a failing build"
if "$SCRIPT" --lib A --lib B --lib C --lib Good -- A B C > produced.out 2>&1; then
  rc=0
else
  rc=$?
fi
cat produced.out
if [ "$rc" -eq 0 ]; then
  echo "FAILURE: expected nonzero exit on build failure"
  exit 1
fi
match_text "Selected-library dependents:" produced.out
match_text "B: 1" produced.out

./clean.sh
