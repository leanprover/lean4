#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# This test covers the use of meta programming utilities in Lean files
# ---

# Test `run_io`
echo "# TEST: run_io"
test_out "impure" resolve-deps -R
test_not_out "impure" resolve-deps

# Test `meta if` and command `do`
echo "# TEST: meta if"
test_not_pat "foo|bar|baz|lorem|ipsum"  resolve-deps -R
test_out "baz" resolve-deps -R -Kbaz
test_out "foo" resolve-deps -R -Kenv=foo
test_out "foo" run print_env
test_out "bar" resolve-deps -R -Kenv=bar
test_out "bar" run print_env

# Test environment extension filtering
# https://github.com/leanprover/lean4/issues/2632

test_out "elabbed-string" run print_elab

# cleanup
rm -f produced.out
