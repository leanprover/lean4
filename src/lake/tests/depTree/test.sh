#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-$PWD/../../.lake/build/bin/lake}

unamestr=`uname`
if [ "$unamestr" = Darwin ] || [ "$unamestr" = FreeBSD ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh

# Test the functionality of Lake's dependency resolution
# in many edge cases with a full tree of dependencies.
# https://github.com/leanprover/lake/issues/70
# https://github.com/leanprover/lake/issues/84
# https://github.com/leanprover/lake/issues/85
# https://github.com/leanprover/lake/issues/119

# a@1/init
$LAKE new a lib.lean
pushd a
git init
git checkout -b master
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in a'
git tag init
popd

# b@1: require a@master, manifest a@1
$LAKE new b lib.lean
pushd b
git init
git checkout -b master
cat >>lakefile.lean <<EOF
require a from git "../a" @ "master"
EOF
$LAKE update -v
grep --color "\"a\"" lake-manifest.json
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in b'
popd

# a@2
pushd a
echo def hello2 := 42 >>A.lean
git commit -am 'second commit in a'
popd

# c@1: require a@master, manifest a@2
$LAKE new c lib.lean
pushd c
git init
git checkout -b master
cat >>lakefile.lean <<EOF
require a from git "../a" @ "master"
EOF
$LAKE update -v
grep --color "\"a\"" lake-manifest.json
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in c'
popd

# d@1: require b@master c@master => a, manifest a@1 b@1 c@1
$LAKE new d lib.lean
pushd d
git init
git checkout -b master
cat >>lakefile.lean <<EOF
require c from git "../c" @ "master"
require b from git "../b" @ "master"
EOF
# make sure we pick up the version from b's manifest (a@1)
$LAKE update -v 2>&1 | grep --color 'first commit in a'
git add .
git config user.name test
git config user.email test@example.com
git commit -am 'first commit in d'
# ensure repeated update is a no-op
$LAKE update -v
git diff --exit-code
popd

# issue 84/85
pushd b
# b: a@1/init -> a@2
$LAKE update -v
# test 84: `lake update` does update
git diff | grep --color manifest
sed_i 's/master/init/g' lakefile.lean
# test 85: warn when manifest and configuration differ
$LAKE resolve-deps -v 2>&1 | grep --color 'manifest out of date'
# b: a@1
git reset --hard
popd

# a@3
pushd a
echo '-- third commit in a' >>A.lean
git commit -am 'third commit in a'
popd

# issue 70
# d@1: a@1 b@1 c@1
pushd d
$LAKE update -v
# test 70: we do not update transitive depednecies
grep --color 'third commit in a' .lake/packages/a/A.lean && exit 1 || true
git diff --exit-code
popd

# issue 119
pushd a
# a@3/master/main
git checkout -b main
popd
pushd b
# b@2: a@master -> a@main
sed_i 's/master/main/' lakefile.lean
$LAKE update a -v
git commit -am 'second commit in b'
popd
pushd a
# a@4/main
sed_i 's/third commit/fourth commit/' A.lean
git commit -am 'fourth commit in a'
popd
pushd c
# c@2
echo '-- second commit in c' >>C.lean
git commit -am 'second commit in c'
popd
pushd d
# d: b@1 -> b@2 => a@1 -> a@3
$LAKE update b -v
# test that Lake does not update c
grep --color 'second commit in c' .lake/packages/c/C.lean && exit 1 || true
# test 119: pickup a@3 and not a@4
grep --color 'third commit in a' .lake/packages/a/A.lean
# test the removal of `c` from the manifest
grep --color "\"c\"" lake-manifest.json
sed_i '/require c/d' lakefile.lean
$LAKE update c -v
grep --color "\"c\"" lake-manifest.json && exit 1 || true
popd
