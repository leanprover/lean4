#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

$LAKE exe hello
$LAKE exe hello Bob Bill
.lake/build/bin/hello

# Tests that quiet mode (-q) produces no output on no-op build
$LAKE -q build hello 2>&1 | diff - /dev/null

# Tests that build produces a manifest if there is none.
# Related: https://github.com/leanprover/lean4/issues/2549
test -f lake-manifest.json

# Test pack/unpack
$LAKE pack .lake/build.tgz 2>&1 | grep --color "packing"
rm -rf .lake/build
$LAKE unpack .lake/build.tgz 2>&1 | grep --color "unpacking"
.lake/build/bin/hello
$LAKE pack 2>&1 | grep --color "packing"
rm -rf .lake/build
$LAKE unpack 2>&1 | grep --color "unpacking"
.lake/build/bin/hello

./clean.sh

$LAKE -f lakefile.toml exe hello
$LAKE -f lakefile.toml exe hello Bob Bill
.lake/build/bin/hello
