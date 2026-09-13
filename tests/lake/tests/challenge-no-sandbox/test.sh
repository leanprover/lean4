#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake comparator needs Linux namespaces"
  exit 0
fi

# User namespaces cannot be assumed available in CI containers; see `../fake-bwrap.sh`.
export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

# Naming a sandbox that is not on PATH takes the same lookup path as having no `bwrap` at all,
# without depending on whether the machine running the tests happens to have one installed.
export COMPARATOR_BWRAP=lake-comparator-missing-sandbox

test_status_out 2 'There is no unsandboxed mode' comparator --config config.json
test_status_out 2 'lake-comparator-missing-sandbox' comparator --config config.json

rm -f produced.out
