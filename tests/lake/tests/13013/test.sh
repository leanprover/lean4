#!/usr/bin/env bash
source ../common.sh
./clean.sh

# This test covers issue 13013
# https://github.com/leanprover/lean4/issues/13013

# Lake (and Lean) rely on module names being unique within a package,
# so this test verifies that Lake produces a clean error on such a configuration,
# rather than supporting it.

# Verify that sharing root module names across executables produces an error.
test_err "shared.toml:9:0: test: executable 'bar' has the same root module 'Main' as executable 'foo'" \
  -f shared.toml build
test_err "test: executable 'bar' has the same root module 'Main' as executable 'foo'" \
  -f shared.lean build

# Verify that unique module names produce distinct executables.
test_run -f unique.toml build
test_cmd_eq "I am foo" ./.lake/build/bin/foo
test_cmd_eq "I am bar" ./.lake/build/bin/bar

# Cleanup
rm -f produced.out
