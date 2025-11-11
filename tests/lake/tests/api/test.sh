#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Run DSL tests
test_run -f keys.lean resolve-deps

# Run Lean tests
test_run env lean vers.lean
