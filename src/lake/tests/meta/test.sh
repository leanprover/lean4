#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

unamestr=`uname`
if [ "$unamestr" = Darwin ] || [ "$unamestr" = FreeBSD ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi


./clean.sh

# ===
# Test the use of meta utilities in Lake configuration files
# ===

# --
# Conditional dependencies
# --

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the bar repository on each test. This requires updating the
# locked manifest to the new hash to ensure things work properly.
pushd foo
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
GIT_REV=`git rev-parse HEAD`
popd

# test `meta if require` / `require if`
$LAKE resolve-deps -R 2>&1 | grep --color 'the following syntax is deprecated:'
# check that the creation/update of the manifest materializes the dependency
test -d .lake/packages/foo
# ensure the manifest contains the conditional dependency
LOCKED_REV='b89452b44125611e3876e9f9f27a1726effa2440'
sed_i "s/$GIT_REV/$LOCKED_REV/g" lake-manifest.json
diff --strip-trailing-cr lake-manifest.expected.json lake-manifest.json
sed_i "s/$LOCKED_REV/$GIT_REV/g" lake-manifest.json
# check that a simple materialziation does not clone the conditional dependency
rm -rf .lake
$LAKE resolve-deps -R
test ! -d .lake/packages/foo
# check enabling the conditional dependency works
$LAKE resolve-deps -R -KreqFoo
test -d .lake/packages/foo

# ---
# Configuration-time command elaborators
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
