#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

unamestr=`uname`
if [ "$unamestr" = Darwin ] || [ "$unamestr" = FreeBSD ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the bar repository on each test. This requires updating the
# locked manifest to the new hash to ensure things work properly.
pushd bar
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
GIT_REV=`git rev-parse HEAD`
popd

LOCKED_REV='0538596b94a0510f55dc820cabd3bde41ad93c3e'

# ---
# Test manifest manually upgrades from unsupported versions
# ---

# Test loading of a V4 manifest fails
cp lake-manifest-v4.json lake-manifest.json
($LAKE resolve-deps 2>&1 && exit 1 || true) | grep "incompatible manifest version '4'"

# Test package update fails as well
($LAKE update bar 2>&1 && exit 1 || true) | grep "incompatible manifest version '4'"

# Test bare update produces the expected V7 manifest
$LAKE update
sed_i "s/$GIT_REV/$LOCKED_REV/g" lake-manifest.json
diff --strip-trailing-cr lake-manifest-v7.json lake-manifest.json
rm -rf .lake

# ---
# Test manifest automatically upgrades from supported versions
# ---

# Test successful loading of a V5 manifest
cp lake-manifest-v5.json lake-manifest.json
sed_i "s/253735aaee71d8bb0f29ae5cfc3ce086a4b9e64f/$GIT_REV/g" lake-manifest.json
$LAKE resolve-deps

# Test update produces the expected V7 manifest
$LAKE update
sed_i "s/$GIT_REV/$LOCKED_REV/g" lake-manifest.json
diff --strip-trailing-cr lake-manifest-v7.json lake-manifest.json

# Test successful loading of a V6 manifest
cp lake-manifest-v6.json lake-manifest.json
sed_i "s/dab525a78710d185f3d23622b143bdd837e44ab0/$GIT_REV/g" lake-manifest.json
$LAKE resolve-deps

# Test update produces the expected V7 manifest
$LAKE update
sed_i "s/$GIT_REV/$LOCKED_REV/g" lake-manifest.json
diff --strip-trailing-cr lake-manifest-v7.json lake-manifest.json
