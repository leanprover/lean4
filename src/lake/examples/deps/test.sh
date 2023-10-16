#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

$LAKE -d bar build --update
$LAKE -d foo build --update

./foo/build/bin/foo
./bar/build/bin/bar

# Test print-paths works (i.e., does not error)
$LAKE -d foo print-paths A B

# Test `lake clean`
test -d a/build
test -d b/build
$LAKE -d foo clean a b
test ! -d a/build
test ! -f a/lakefile.olean
test ! -d b/build
test ! -f b/lakefile.olean
test -d root/build
test -f root/lakefile.olean
test -d foo/build
test -f foo/lakefile.olean
$LAKE -d foo clean
test ! -d root/build
test ! -f root/lakefile.olean
test ! -d foo/build
test ! -f foo/lakefile.olean
