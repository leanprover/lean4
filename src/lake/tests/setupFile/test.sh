#!/usr/bin/env bash
source ../common.sh

./clean.sh

#---
# Test `setup-file` functionality
#---

# Test that, by default, no plugins are used.
test_out '"plugins":[]' setup-file ImportFoo.lean

# Test that, by default, no dynlibs are used.
test_out '"dynlibs":[]' setup-file ImportFoo.lean

# Test that, generally, no options are set.
test_out '"options":{}' setup-file ImportFoo.lean

# Test that a more specific configuration will be used if
# Lake can identify the module corresponding to the path.
test_out '"options":{"weak.foo":"bar"}' setup-file Test.lean

# Test that `setup-file` on an invalid Lean configuration file succeeds.
test_run -f invalid.lean setup-file invalid.lean

# Test that `setup-file` on a configuration file uses the Lake plugin,
# even if the file is invalid and/or is not using a `Lake` import.
test_not_out '"plugins":[]' -f invalid.lean setup-file invalid.lean

# Test that when a header is provided (via CLI or stdin),
# it will be used instead of the file's header for an external module.
test_out '"isModule":false' setup-file ImportFoo.lean
HEADER_JSON='{"isModule":true,"imports":[]}'
test_out '"isModule":true' setup-file ImportFoo.lean "$HEADER_JSON"
echo "$HEADER_JSON" | test_out '"isModule":true' setup-file ImportFoo.lean -
BOGUS_JSON='{"isModule":false,"imports":[{"module":"Test.Bogus","isMeta":false,"isExported":true,"importAll":false}]}'
test_err 'no such file or directory' setup-file ImportFoo.lean "$BOGUS_JSON"

# Test that when a header is provided (via CLI or stdin),
# the header is *NOT* used for an internal module and its imports are not built.
# TODO: Use the provided header.
test_out '"isModule":false' setup-file Test.lean
test_out '"isModule":false' setup-file Test.lean "$HEADER_JSON"
echo "$HEADER_JSON" | test_out '"isModule":false' setup-file Test.lean -
# If the provided import (Test.Bogus) was built, this would fail.
test_run setup-file Test.lean "$BOGUS_JSON"

# Cleanup
rm -f produced.out
