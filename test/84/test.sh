#!/usr/bin/env bash
set -exo pipefail

LAKE1=${LAKE:-../../../build/bin/lake}
LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

$LAKE new a
pushd a
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in a'
popd

$LAKE new b
pushd b
cat >>lakefile.lean <<EOF
require a from git "../a" @ "master"
EOF
$LAKE1 update
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in b'
popd

pushd a
echo def hello2 := 42 >>A.lean
git commit -am 'second commit in a'
popd

pushd b
$LAKE1 update
git diff | grep -m1 manifest
popd
