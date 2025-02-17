#!/usr/bin/env bash
set -euxo pipefail

./clean.sh

unamestr=`uname`
if [ "$unamestr" = Darwin ] || [ "$unamestr" = FreeBSD ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

LAKE1=${LAKE:-../../../.lake/build/bin/lake}
LAKE=${LAKE:-../../.lake/build/bin/lake}

# Test `new` and `init` with bad template/language (should error)

($LAKE new foo bar 2>&1 && exit 1 || true) | grep --color "unknown package template"
($LAKE new foo .baz 2>&1 && exit 1 || true) | grep --color "unknown configuration language"
($LAKE init foo bar 2>&1 && exit 1 || true) | grep --color "unknown package template"
($LAKE init foo std.baz 2>&1 && exit 1 || true) | grep --color "unknown configuration language"

# Test package name validation (should error)
# https://github.com/leanprover/lean4/issues/2637

($LAKE new  .    2>&1 && exit 1 || true) | grep --color "illegal package name"
for cmd in new init; do
($LAKE $cmd ..   2>&1 && exit 1 || true) | grep --color "illegal package name"
($LAKE $cmd .... 2>&1 && exit 1 || true) | grep --color "illegal package name"
($LAKE $cmd '  ' 2>&1 && exit 1 || true) | grep --color "illegal package name"
($LAKE $cmd a/bc 2>&1 && exit 1 || true) | grep --color "illegal package name"
($LAKE $cmd a\\b 2>&1 && exit 1 || true) | grep --color "illegal package name"
($LAKE $cmd init 2>&1 && exit 1 || true) | grep --color "reserved package name"
($LAKE $cmd Lean 2>&1 && exit 1 || true) | grep --color "reserved package name"
($LAKE $cmd Lake 2>&1 && exit 1 || true) | grep --color "reserved package name"
($LAKE $cmd main 2>&1 && exit 1 || true) | grep --color "reserved package name"
done

# Test default (std) template

$LAKE new hello .lean
$LAKE -d hello exe hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello
$LAKE new hello .toml
$LAKE -d hello exe hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello

# Test exe template

$LAKE new hello exe.lean
test -f hello/Main.lean
$LAKE -d hello exe hello
rm -rf hello
$LAKE new hello exe.toml
test -f hello/Main.lean
$LAKE -d hello exe hello
rm -rf hello

# Test lib template

$LAKE new hello lib.lean
$LAKE -d hello build Hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello
$LAKE new hello lib.toml
$LAKE -d hello build Hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello

# Test math template

$LAKE new qed math.lean || true # ignore toolchain download errors
# Remove the require, since we do not wish to download mathlib during tests
sed_i '/^require.*/{N;d;}' qed/lakefile.lean
$LAKE -d qed build Qed
test -f qed/.lake/build/lib/lean/Qed.olean
rm -rf qed
$LAKE new qed math.toml || true # ignore toolchain download errors
# Remove the require, since we do not wish to download mathlib during tests
sed_i '/^\[\[require\]\]/{N;N;N;d;}' qed/lakefile.toml
$LAKE -d qed build Qed
test -f qed/.lake/build/lib/lean/Qed.olean

# Test `init .`

mkdir hello
pushd hello
$LAKE1 init .
$LAKE1 exe hello
popd

# Test creating packages with uppercase names
# https://github.com/leanprover/lean4/issues/2540

$LAKE new HelloWorld
$LAKE -d HelloWorld exe helloworld

# Test creating multi-level packages with a `.`

$LAKE new hello.world
$LAKE -d hello-world exe hello-world
test -f hello-world/Hello/World/Basic.lean

$LAKE new hello.exe exe
$LAKE -d hello-exe exe hello-exe

# Test creating packages with a `-` (i.e., a non-identifier package name)
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20new.20lean-data

$LAKE new lean-data
$LAKE -d lean-data exe lean-data

# Test creating packages starting with digits (i.e., a non-identifier library name)
# https://github.com/leanprover/lean4/issues/2865

$LAKE new 123-hello
$LAKE -d 123-hello exe 123-hello

# Test creating packages with components that contain `.`s
# https://github.com/leanprover/lean4/issues/2999

# the unicode name is improperly encoded on windows for non-Lake reasons
if [ "$OSTYPE" != "msys" ]; then
  $LAKE new «A.B».«C.D»
  $LAKE -d A-B-C-D exe a-b-c-d
fi

# Test creating packages with keyword names
# https://github.com/leanprover/lake/issues/128

$LAKE new meta
$LAKE -d meta exe meta

# Test `init` with name

mkdir hello_world
pushd hello_world
$LAKE1 init hello_world exe
$LAKE1 exe hello_world
popd

# Test bare `init` on existing package (should error)

($LAKE -d hello_world init 2>&1 && exit 1 || true) | grep --color "package already initialized"
