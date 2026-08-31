#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake challenge needs Linux Landlock"
  exit 0
fi

# Landlock cannot be assumed available in CI containers; see `../fake-landrun.sh`.
export COMPARATOR_LANDRUN="$PWD/../fake-landrun.sh"

# Naming a sandbox that is not on PATH takes the same lookup path as having no `landrun` at all,
# without depending on whether the machine running the tests happens to have one installed.
export COMPARATOR_LANDRUN=lake-challenge-missing-sandbox

test_status_out 2 'There is no unsandboxed mode' challenge --config config.json
test_status_out 2 'lake-challenge-missing-sandbox' challenge --config config.json

rm -f produced.out
