#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

$LAKE -d bar build --update
# Test that the update produces the expected manifest.
# Serves as a regression test to ensure that multiples of a package in
# the dependency tree do not produce duplicate entries in the manifest.
# https://github.com/leanprover/lean4/pull/3957
diff -u --strip-trailing-cr bar/lake-manifest.expected.json bar/lake-manifest.json
$LAKE -d foo build --update

./foo/.lake/build/bin/foo
./bar/.lake/build/bin/bar

# Test setup-file works (i.e., does not error)
$LAKE -d foo setup-file ./foo/Foo.lean A B

# Test `lake clean`
test -d a/.lake/build
test -d b/.lake/build
$LAKE -d foo clean a b
test ! -d a/.lake/build
test ! -d b/.lake/build
test -d root/.lake/build
test -d foo/.lake/build
$LAKE -d foo clean
test ! -d root/.lake/build
test ! -d foo/.lake/build

./clean.sh

$LAKE -d bar -f lakefile.toml build --update
diff -u --strip-trailing-cr bar/lake-manifest.expected.json bar/lake-manifest.json
$LAKE -d foo -f lakefile.toml build --update

./foo/.lake/build/bin/foo
./bar/.lake/build/bin/bar
