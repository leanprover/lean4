#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# Test the behavior of `lake query`
# ---

echo "# COMMON TESTS"

# Test failure to build a query-only target
test_err "not a build target" build +A:imports

# Test querying a custom target
test_eq "foo" query foo
test_eq '"foo"' query foo --json

# Test querying imports
test_eq "B" query +A:imports
test_eq '["C","B"]' query +A:transImports --json

# Test querying deps
test_eq "dep" query :deps
test_eq '["dep.1"]' query :transDeps --json

echo "# UNCOMMON TESTS"
set -x

# Check that logs are not written to stdout
$LAKE query | diff - /dev/null

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

set +x

# Cleanup
rm -f produced.out
