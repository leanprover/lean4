#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test loading the same dependency with different names
test_run update
test_eq 'a' query @a/name
test_eq 'b' query @b/name

# cleanup
rm -f produced.out
