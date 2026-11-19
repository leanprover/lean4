#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "$OS" = Windows_NT ]; then
  echo "Skipping test: lake comparator needs env and git on PATH"
  exit 0
fi

export COMPARATOR_BWRAP=lake-comparator-no-such-sandbox

"$LAKE" resolve-deps

test_status_out 0 'Your solution is okay!' comparator --config config.json --inadvisably-no-sandbox
match_text 'WARNING: Sandbox disabled' produced.out

if [ "$UNAME" = Linux ]; then
  test_status_out 2 'lake-comparator-no-such-sandbox' comparator --config config.json
fi

rm -f produced.out
