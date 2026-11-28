#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "$OS" = Windows_NT ]; then
  echo "Skipping test: lake check needs env and git on PATH"
  exit 0
fi

"$LAKE" resolve-deps

# `Solution.lean` fails to build if it gets at something the sandbox denies, as it does without one.
test_status_out 1 'sandbox escape: wrote to the project directory' check --inadvisably-no-sandbox

if [ "$UNAME" != Darwin ]; then
  echo "Skipping the rest of the test: fake-bwrap.sh does not isolate the build"
  ./clean.sh
  exit 0
fi

./clean.sh
init_check_sandbox
"$LAKE" resolve-deps

# `Solution.lean` tries to get at this file.
SECRET=/private/tmp/_tmp_lake_check_sandbox_secret
echo secret > "$SECRET"
trap 'rm -f "$SECRET"' EXIT

test_status_out 0 'Lean default kernel accepts the solution' check
test_exp ! -e _tmp_escape
test_exp -f "$SECRET"

rm -f produced.out
