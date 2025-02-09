#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the `bar1` repository on each test.
pushd bar1
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
popd

$LAKE resolve-deps -R
$LAKE exe bar | grep --color "bar1"

$LAKE resolve-deps -R -Kfoo --packages=packages.json
$LAKE --packages=packages.json exe bar  | grep --color "bar2"
$LAKE --packages=packages.json exe foo  | grep --color "foo"

$LAKE resolve-deps -R
$LAKE exe bar | grep --color "bar1"

cp packages.json .lake/package-overrides.json
$LAKE resolve-deps -R -Kfoo
$LAKE exe bar | grep --color "bar2"
$LAKE exe foo | grep --color "foo"
