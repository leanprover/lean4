set -ex

./clean.sh

LAKE1=${LAKE:-../../../.lake/build/bin/lake}
LAKE=${LAKE:-../../.lake/build/bin/lake}

# Test `new` and `init` with bad template (should error)

! $LAKE new foo bar
! $LAKE init foo bar

# Test creating packages with uppercase names
# https://github.com/leanprover/lean4/issues/2540

$LAKE new Hello
$LAKE -d Hello build
Hello/.lake/build/bin/hello

# Test creating multi-level packages with a `.`

$LAKE new hello.world
$LAKE -d hello-world build
hello-world/.lake/build/bin/hello-world
test -f hello-world/Hello/World/Basic.lean

# Test creating packages with a `-` (i.e., a non-Lean name)
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20new.20lean-data

$LAKE new lean-data
$LAKE -d lean-data build
lean-data/.lake/build/bin/lean-data

# Test creating packages with keyword names
# https://github.com/leanprover/lake/issues/128

$LAKE new meta
$LAKE -d meta build
meta/.lake/build/bin/meta

# Test `init`

mkdir hello_world

cd hello_world
$LAKE1 init hello_world exe
$LAKE1 build
./.lake/build/bin/hello_world

# Test `init` on existing package (should error)

$LAKE1 init hello_world && exit 1 || true
