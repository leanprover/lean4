#!/usr/bin/env bash
source ../common.sh

./clean.sh

#---
# Test `setup-file` functionality
#---

# Test that, by default, no plugins are used.
test_out '"pluginPaths":[]' setup-file bogus Foo

# Test that, by default, no dynlibs are used.
test_out '"loadDynlibPaths":[]' setup-file bogus Foo

# Test that, generally, no options are set.
test_out '"setupOptions":{}' setup-file bogus Foo

# Test that a more specific configuration will be used if
# Lake can indentify the module corresponding to the path.
test_out '"setupOptions":{"weak.foo":"bar"}' setup-file Test.lean

# Test that `setup-file` on an invalid Lean configuration file succeeds.
test_run -f invalid.lean setup-file invalid.lean Lake

# Test that `setup-file` on a configuration file uses the Lake plugin,
# even if the file is invalid and/or is not using a `Lake` import.
test_not_out '"pluginPaths":[]' -f invalid.lean setup-file invalid.lean

# Cleanup
rm -f produced.out
