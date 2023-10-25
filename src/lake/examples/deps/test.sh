#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

$LAKE -d bar build --update
$LAKE -d foo build --update

./foo/.lake/build/bin/foo
./bar/.lake/build/bin/bar

# Test print-paths works (i.e., does not error)
$LAKE -d foo print-paths A B

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
