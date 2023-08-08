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
