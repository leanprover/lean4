#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "$OS" = Windows_NT ]; then
  echo "Skipping test: lake check needs env and git on PATH"
  exit 0
fi

export COMPARATOR_BWRAP=lake-check-no-such-sandbox

"$LAKE" resolve-deps

test_status_out 0 'Lean default kernel accepts the solution' check --inadvisably-no-sandbox
match_text 'WARNING: Sandbox disabled' produced.out
match_text 'Uses axioms: Classical.choice, propext, Quot.sound' produced.out

if [ "$UNAME" = Linux ]; then
  test_status_out 2 'lake-check-no-such-sandbox' check
fi

rm -f produced.out
