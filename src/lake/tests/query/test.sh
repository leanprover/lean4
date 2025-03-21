#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# Test the behavior of `lake query`
# ---

# Check that logs are not written to stdout
$LAKE query | diff - /dev/null

# Test failure to build a query-only target
($LAKE build +A:imports 2>&1 && exit 1 || true) | grep --color "not a build target"

# Test querying a custom target
test "`$LAKE query foo`" = foo
test "`$LAKE query foo --json`" = '"foo"'

# Test querying imports
test "`$LAKE query +A:imports`" = B
test "`$LAKE query +A:transImports --json`" = '["C","B"]'

# Test querying library modules
$LAKE query lib:modules | sort | diff -u --strip-trailing-cr <(cat << 'EOF'
A
B
C
EOF
) -

# Test that querying an executable
# returns its path which can then be executed
`$LAKE query a`

# Test querying multiple targets
test `$LAKE query foo foo | wc -l` = 2
test `$LAKE query a b | wc -l` = 2
