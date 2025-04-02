#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# This test covers the use of meta programming utilities in Lean files
# ---

# Test `run_io`
$LAKE resolve-deps -R 2>&1 | grep --color impure
$LAKE resolve-deps 2>&1 | (grep --color impure && exit 1 || true)

# Test `meta if` and command `do`
$LAKE resolve-deps -R 2>&1 | (grep --color -E "foo|bar|baz|lorem|ipsum" && exit 1 || true)
$LAKE resolve-deps -R -Kbaz 2>&1 | grep --color baz
$LAKE resolve-deps -R -Kenv=foo 2>&1 | grep --color foo
$LAKE run print_env 2>&1 | grep --color foo
$LAKE resolve-deps -R -Kenv=bar 2>&1 | grep --color bar
$LAKE run print_env 2>&1 | grep --color bar

# Test environment extension filtering
# https://github.com/leanprover/lean4/issues/2632

$LAKE run print_elab 2>&1 | grep --color elabbed-string
