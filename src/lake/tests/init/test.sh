set -ex

./clean.sh

LAKE1=${LAKE:-../../../build/bin/lake}
LAKE=${LAKE:-../../build/bin/lake}

# Test `new` and `init` with bad template (should error)

$LAKE new foo bar && exit 1 || true
$LAKE init foo bar && exit 1 || true

# Test `new` with `.`

$LAKE new hello.world
$LAKE -d hello-world build
hello-world/build/bin/hello-world

# Test `new` with `-`
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20new.20lean-data

$LAKE new lean-data
$LAKE -d lean-data build
lean-data/build/bin/lean-data

# Test issue 128

$LAKE new meta
$LAKE -d meta build
meta/build/bin/meta

# Test `init`

mkdir hello_world

cd hello_world
$LAKE1 init hello_world exe
$LAKE1 build
./build/bin/hello_world

# Test `init` on existing package (should error)

$LAKE1 init hello_world && exit 1 || true
