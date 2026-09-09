#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake challenge needs Linux Landlock"
  exit 0
fi

# Landlock cannot be assumed available in CI containers; see `../fake-landrun.sh`.
export COMPARATOR_LANDRUN="$PWD/../fake-landrun.sh"

# A configuration that is not JSON at all.
test_status_out 2 'malformed configuration' challenge --config malformed.json

# A configuration that parses but leaves out a required key.
test_status_out 2 'solution_module' challenge --config incomplete.json

# A configuration that is not there.
test_status_out 2 'could not read the configuration' challenge --config absent.json

# No configuration at all.
test_status_out 2 'pass `--config <file>`' challenge

rm -f produced.out
