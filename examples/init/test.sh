set -ex

./clean.sh

LAKE1=${LAKE:-../../../build/bin/lake}
LAKE=${LAKE:-../../build/bin/lake}

# Test `new` and `init` with bad template (should error)

$LAKE new foo bar && exit 1 || true
$LAKE init foo bar && exit 1 || true

# Test `new`

$LAKE new hello.world
$LAKE -d hello-world build
hello-world/build/bin/hello-world

# Test `init`

mkdir hello_world

cd hello_world
$LAKE1 init hello_world exe
$LAKE1 build
./build/bin/hello_world

# Test `init` on existing package (should error)

$LAKE1 init hello_world && exit 1 || true
