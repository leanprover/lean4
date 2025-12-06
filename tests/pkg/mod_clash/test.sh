#!/usr/bin/env bash
source ../../lake/tests/common.sh

# This test covers importing modules which are defined in multiple packages
# (with the same original package name).

./clean.sh
test_run resolve-deps

# Test that importing a module with multiple identical candidates works
test_run build Test.ImportSame

# Test that importing a module with multiple sufficiently similar candidates works
test_run build Test.ImportSimilar

# Test that importing a module with multiple distinct candidates fails
test_err 'could not disambiguate the module `Diff`' build Test.ImportDiff
