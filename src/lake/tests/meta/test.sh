#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# This test covers the use of meta programming utilities in Lean files
# ---

# Test `run_io`
$LAKE resolve-deps -R 2>&1 | grep impure
$LAKE resolve-deps 2>&1 | (grep impure && false || true)

# Test `meta if` and command `do`
$LAKE resolve-deps -R 2>&1 | (grep -E "foo|bar|baz|1|2" && false || true)
$LAKE resolve-deps -R -Kbaz 2>&1 | grep baz
$LAKE resolve-deps -R -Kenv=foo 2>&1 | grep foo
$LAKE run print_env 2>&1 | grep foo
$LAKE resolve-deps -R -Kenv=bar 2>&1 | grep bar
$LAKE run print_env 2>&1 | grep bar

# Test environment extension filtering
# https://github.com/leanprover/lean4/issues/2632

$LAKE run print_elab 2>&1 | grep elabbed-string
