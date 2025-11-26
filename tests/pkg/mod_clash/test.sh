#!/usr/bin/env bash
source ../../lake/tests/common.sh

# This test covers importing modules which are defined in multiple packages.

./clean.sh
test_run resolve-deps

# Test that importing a module with multiple equivalent candidates works
test_run build Test.ImportSame

# Test that importing a module with multiple distinct candidates fails
test_err 'Unknown identifier `foo`' build Test.ImportDiff
