#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake challenge needs Linux Landlock"
  exit 0
fi

# Landlock cannot be assumed available in CI containers; see `../fake-landrun.sh`.
export COMPARATOR_LANDRUN="$PWD/../fake-landrun.sh"

# `lake challenge` resolves dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first. Building the project once does the same;
# this just skips the build.
"$LAKE" resolve-deps

test_status_out 1 "Illegal axiom detected: 'sorryAx'" challenge --config config.json

rm -f produced.out
