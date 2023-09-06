#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

if [ "`uname`" = Darwin ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh

mkdir hello
pushd hello
$LAKE init hello
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
popd

cd test

# test git clone
$LAKE update
test -d lake-packages/hello
$LAKE build
./build/bin/test

# test leanprover/lake#167
sed_i "s/Hello,/Goodbye,/" lake-packages/hello/Main.lean
! git -C lake-packages/hello diff --exit-code
$LAKE build 2>&1 | grep -m1 "has local changes"
./build/bin/test

# test leanprover/lake#104
TEST_URL=https://example.com/hello.git
MANIFEST=lake-manifest.json

$LAKE update
$LAKE build
cat $MANIFEST
sed_i "s,\\.\\.[^\"]*,$TEST_URL," $MANIFEST
cat $MANIFEST
# set invalid remote
git -C lake-packages/hello remote set-url origin $TEST_URL
# should still succeed (do nothing) as remote should not be fetched
$LAKE build -Kurl=$TEST_URL
