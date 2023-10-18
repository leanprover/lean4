#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

if [ "`uname`" = Darwin ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh

# Test Lake's management of a single Git-cloned dependency.

mkdir hello
pushd hello
$LAKE init hello
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
popd

HELLO_MAP="{\"hello\" : \"file://$(pwd)/hello\"}"

cd test

# test that `LAKE_PKG_URL_MAP` properly overwrites the config-specified Git URL
LAKE_PKG_URL_MAP=$HELLO_MAP $LAKE update | grep "file://"
# test that a second `lake update` is a no-op (with URLs)
# see https://github.com/leanprover/lean4/commit/6176fdba9e5a888225a23e5d558a005e0d1eb2f6#r125905901
LAKE_PKG_URL_MAP=$HELLO_MAP $LAKE update | diff - /dev/null
rm -rf lake-packages

# Test that Lake produces no warnings on a `lake build` after a `lake update`
# See https://github.com/leanprover/lean4/issues/2427

$LAKE update
# test that a second `lake update` is a no-op (with file paths)
$LAKE update | diff - /dev/null
test -d lake-packages/hello
# test that Lake produces no warnings
$LAKE build 3>&1 1>&2 2>&3 | diff - /dev/null
./build/bin/test | grep "Hello, world"

# Test that Lake produces a warning if local changes are made to a dependency
# See https://github.com/leanprover/lake/issues/167

sed_i "s/world/changes/" lake-packages/hello/Hello/Basic.lean
! git -C lake-packages/hello diff --exit-code
$LAKE build 3>&1 1>&2 2>&3 | grep "has local changes"
./build/bin/test | grep "Hello, changes"
git -C lake-packages/hello reset --hard
$LAKE build 3>&1 1>&2 2>&3 | diff - /dev/null

# Test no `git fetch` on a `lake build` if already on the proper revision
# See https://github.com/leanprover/lake/issues/104

TEST_URL=https://example.com/hello.git
TEST_MAP="{\"hello\" : \"$TEST_URL\"}"

# set invalid remote
git -C lake-packages/hello remote set-url origin $TEST_URL
# build should succeed (do nothing) despite the invalid remote because
# the remote should not be fetched; Lake should also not produce any warnings
LAKE_PKG_URL_MAP=$TEST_MAP $LAKE build 3>&1 1>&2 2>&3 | diff - /dev/null
