#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./setup.sh

# Test initial directory structure
$LAKE exe test | diff -u --strip-trailing-cr <(cat << 'EOF'
foo
bar
baz
untraced
untraced
EOF
) -

# Test input file dependency
echo traced > inputs/foo.txt
test "$LAKE exe test foo" = "traced"

# Test input directory dependency
echo traced > inputs/barz/bar.txt
test "$LAKE exe test bar" = "traced"
echo traced > inputs/barz/baz.txt
test "$LAKE exe test baz" = "traced"

# Test untraced dependencies
echo traced > inputs/untraced.txt
echo traced > inputs/barz/untraced.txt
$LAKE exe test | diff -u --strip-trailing-cr <(cat << 'EOF'
traced
traced
traced
untraced
untraced
EOF
) -
