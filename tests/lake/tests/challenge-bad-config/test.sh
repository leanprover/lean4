#!/usr/bin/env bash
source ../common.sh

./clean.sh

init_check_sandbox

# A configuration that is not JSON at all.
test_status_out 2 'malformed configuration' comparator --config malformed.json

# A configuration that parses but leaves out a required key.
test_status_out 2 'solution_module' comparator --config incomplete.json

# A configuration that is not there.
test_status_out 2 'could not read the configuration' comparator --config absent.json

# No configuration at all.
test_status_out 2 'comparator.json' comparator

rm -f produced.out
