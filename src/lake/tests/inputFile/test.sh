#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./setup.sh

# Validate configuration
$LAKE -q resolve-deps 2>&1 | diff - /dev/null

# Test initial directory structure
$LAKE exe test | diff -u --strip-trailing-cr <(cat << 'EOF'
foo
bar
baz
untraced
untraced
EOF
) -

# Validate Lean configuration
$LAKE -f lakefileAlt.lean translate-config toml lakefileAlt.produced.toml 2>&1 | diff - /dev/null
diff -u --strip-trailing-cr lakefileAlt.expected.toml lakefileAlt.produced.toml
$LAKE -f lakefileAlt.lean -q build --no-build 2>&1 | diff - /dev/null

# Validate TOML->Lean translation
$LAKE translate-config lean lakefile.produced.lean 2>&1 | diff - /dev/null
diff -u --strip-trailing-cr lakefile.expected.lean lakefile.produced.lean
$LAKE -f lakefile.expected.lean -q build --no-build 2>&1 | diff - /dev/null

# Test input file target
cat "`$LAKE query foo`" | diff -u --strip-trailing-cr <(echo foo) -

# Test input directory target
cat `$LAKE query barz` | diff -u --strip-trailing-cr <(cat << 'EOF'
bar
baz
EOF
) -

# Test input file dependency
echo traced > inputs/foo.txt
$LAKE exe test foo | diff -u --strip-trailing-cr <(echo traced) -

# Test input directory dependency
echo traced > inputs/barz/bar.txt
$LAKE exe test bar | diff -u --strip-trailing-cr <(echo traced) -
echo traced > inputs/barz/baz.txt
$LAKE exe test baz | diff -u --strip-trailing-cr <(echo traced) -

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
