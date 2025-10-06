#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the bar repository on each test. This requires updating the
# locked manifest to the new hash to ensure things work properly.
echo "# SETUP"
set -x
pushd bar
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
GIT_REV=`git rev-parse HEAD`
popd
set +x

LOCKED_REV='0538596b94a0510f55dc820cabd3bde41ad93c3e'

# Test an update produces the expected manifest of the latest version
test_update() {
  test_run update
  sed_i "s/$GIT_REV/$LOCKED_REV/g" lake-manifest.json
  diff --strip-trailing-cr lake-manifest-latest.json lake-manifest.json
}

# ---
# Test manifest manually upgrades from unsupported versions
# ---

# Test loading of a V4 manifest fails
cp lake-manifest-v4.json lake-manifest.json
test_err "incompatible manifest version '0.4.0'" resolve-deps

# Test package update fails as well
test_err "incompatible manifest version '0.4.0'" update bar

# Test bare update works
test_update
rm -rf .lake

# ---
# Test manifest automatically upgrades from supported versions
# ---

# Test successful load & update of a supported manifest version
test_manifest() {
  cp lake-manifest-$1.json lake-manifest.json
  sed_i "s/$LOCKED_REV/$GIT_REV/g" lake-manifest.json
  test_run resolve-deps
  test_update
}

test_manifest v5
test_manifest v6
test_manifest v7
test_manifest v1.0.0
test_manifest v1.1.0

# cleanup
rm -f produced.out
