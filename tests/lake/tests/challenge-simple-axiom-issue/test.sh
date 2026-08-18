#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake challenge needs Linux Landlock"
  exit 0
fi

# Landlock cannot be assumed available in CI containers; see `../fake-landrun.sh`.
export COMPARATOR_LANDRUN="$PWD/../fake-landrun.sh"

test_status_out 1 "Illegal axiom detected: 'helper'" challenge --config config.json

rm -f produced.out
