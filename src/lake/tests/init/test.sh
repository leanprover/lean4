#!/usr/bin/env bash
set -euxo pipefail

./clean.sh

if [ "`uname`" = Darwin ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

LAKE1=${LAKE:-../../../.lake/build/bin/lake}
LAKE=${LAKE:-../../.lake/build/bin/lake}

# Test `new` and `init` with bad template (should error)

($LAKE new  foo bar 2>&1 && false || true) | grep "unknown package template"
($LAKE init foo bar 2>&1 && false || true) | grep "unknown package template"

# Test package name validation (should error)
# https://github.com/leanprover/lean4/issues/2637

($LAKE new '  ' 2>&1 && false || true) | grep "illegal package name"
($LAKE new .    2>&1 && false || true) | grep "illegal package name"
($LAKE new ..   2>&1 && false || true) | grep "illegal package name"
($LAKE new .... 2>&1 && false || true) | grep "illegal package name"
($LAKE new a/bc 2>&1 && false || true) | grep "illegal package name"
($LAKE new a\\b 2>&1 && false || true) | grep "illegal package name"
($LAKE new init 2>&1 && false || true) | grep "reserved package name"
($LAKE new Lean 2>&1 && false || true) | grep "reserved package name"
($LAKE new Lake 2>&1 && false || true) | grep "reserved package name"
($LAKE new main 2>&1 && false || true) | grep "reserved package name"

# Test `init .`

mkdir hello
pushd hello
$LAKE1 init .
$LAKE1 build
.lake/build/bin/hello
popd

# Test math template

$LAKE new qed math
# Remove the require, since we do not wish to download mathlib during tests
sed_i '/^require.*/{N;d;}' qed/lakefile.lean
$LAKE -d qed build Qed
test -f qed/.lake/build/lib/Qed.olean

# Test creating packages with uppercase names
# https://github.com/leanprover/lean4/issues/2540

$LAKE new HelloWorld
$LAKE -d HelloWorld build
HelloWorld/.lake/build/bin/helloworld

# Test creating multi-level packages with a `.`

$LAKE new hello.world
$LAKE -d hello-world build
hello-world/.lake/build/bin/hello-world
test -f hello-world/Hello/World/Basic.lean

# Test creating packages with a `-` (i.e., a non-identifier package name)
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20new.20lean-data

$LAKE new lean-data
$LAKE -d lean-data build
lean-data/.lake/build/bin/lean-data

# Test creating packages starting with digits (i.e., a non-identifier library name)
# https://github.com/leanprover/lean4/issues/2865

$LAKE new 123-hello
$LAKE -d 123-hello build
123-hello/.lake/build/bin/123-hello

# Test creating packages with keyword names
# https://github.com/leanprover/lake/issues/128

$LAKE new meta
$LAKE -d meta build
meta/.lake/build/bin/meta

# Test `init` with name

mkdir hello_world
pushd hello_world
$LAKE1 init hello_world exe
$LAKE1 build
./.lake/build/bin/hello_world
popd

# Test bare `init` on existing package (should error)

($LAKE -d hello_world init 2>&1 && false || true) | grep "package already initialized"
