#!/usr/bin/env bash
source  ../common.sh
./clean.sh

# Test `needs` of a module in a dependency
test_err 'Running Dep.A' -f lakefile.lean build modA
test_err 'Running Dep.A' -f lakefile.toml build modA

# Cleanup
rm produced.out
