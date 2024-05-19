set -ex

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

./clean.sh

$LAKE -f lakefile.toml exe hello
$LAKE -f lakefile.toml exe hello Bob Bill
.lake/build/bin/hello
