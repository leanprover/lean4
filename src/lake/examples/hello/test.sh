set -ex

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

$LAKE exe hello
$LAKE exe hello Bob Bill
build/bin/hello

# Tests that build produces a manifest if there is none.
# Related: https://github.com/leanprover/lean4/issues/2549
test -f lake-manifest.json
