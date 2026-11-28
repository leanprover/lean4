#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "$UNAME" != Linux ]; then
  echo "Skipping test: only the Linux sandbox is looked up on PATH"
  exit 0
fi

# Naming a sandbox that is not on PATH takes the same lookup path as having no `bwrap` at all,
# without depending on whether the machine running the tests happens to have one installed.
export COMPARATOR_BWRAP=lake-comparator-missing-sandbox

test_status_out 2 'lake-comparator-missing-sandbox' comparator --config config.json

rm -f produced.out
