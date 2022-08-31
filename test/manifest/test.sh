#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-$PWD/../../build/bin/lake}

if [ "`uname`" = Darwin ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh

# tests issues:
# https://github.com/leanprover/lake/issues/70
# https://github.com/leanprover/lake/issues/84
# https://github.com/leanprover/lake/issues/85

$LAKE new a lib
pushd a
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in a'
git tag init
popd

$LAKE new b lib
pushd b
cat >>lakefile.lean <<EOF
require a from git "../a" @ "master"
EOF
$LAKE update -v
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in b'
popd

pushd a
echo def hello2 := 42 >>A.lean
git commit -am 'second commit in a'
popd

$LAKE new c lib
pushd c
cat >>lakefile.lean <<EOF
require a from git "../a" @ "master"
EOF
$LAKE update -v
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in c'
popd

$LAKE new d lib
pushd d
cat >>lakefile.lean <<EOF
require b from git "../b" @ "master"
require c from git "../c" @ "master"
EOF
$LAKE update -v 2>&1 | grep -m8 -E '`[abc]`|master'
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in d'
$LAKE update -v
git diff --exit-code
popd

# issue 85
pushd b
$LAKE update -v
git diff | grep -m1 manifest
sed_i 's/master/init/g' lakefile.lean
$LAKE resolve-deps -v 2>&1 | grep -m1 'listed in manifest does not match `init`'
git reset --hard
popd
