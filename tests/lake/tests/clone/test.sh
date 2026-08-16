#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test Lake's management of a single Git-cloned dependency.

echo "# SETUP"
mkdir hello
pushd hello
$LAKE init hello
rm -f lean-toolchain
$LAKE update
init_git
# `--filter` is silently ignored by a server that does not allow it
git config uploadpack.allowFilter true
# add revisions for the tests to switch between
echo v1 > extra.txt
git add extra.txt
git commit -q -m "extra v1"
REV_A=$(git rev-parse HEAD)
OLD_BLOB=$(git rev-parse HEAD:extra.txt)
echo v2 > extra.txt
git add extra.txt
git commit -q -m "extra v2"
REV_B=$(git rev-parse HEAD)
popd

HELLO_MAP="{\"hello\" : \"file://$(pwd)/hello\"}"

cd test

echo "# TESTS"

# test that `LAKE_PKG_URL_MAP` properly overwrites the config-specified Git URL
LAKE_PKG_URL_MAP=$HELLO_MAP test_out "file://" update
# test that a second `lake update` does not perform another checkout (with URLs)
LAKE_PKG_URL_MAP=$HELLO_MAP test_not_out "checking out" update --keep-toolchain
rm -rf .lake/packages

# Test that Lake produces no warnings on a `lake build` after a `lake update`
# See https://github.com/leanprover/lean4/issues/2427

echo "# TEST: lake build after update"

test_run update
# test that a second `lake update` does not perform another checkout (with file paths)
test_not_out "checking out" update --keep-toolchain
test_exp -d .lake/packages/hello
# test that Lake produces no logs
test_no_stderr build
test_cmd_eq "Hello, world!" ./.lake/build/bin/test

# Test that Lake produces a warning if local changes are made to a dependency
# See https://github.com/leanprover/lake/issues/167

echo "# TEST: Local changes"

sed_i "s/world/changes/" .lake/packages/hello/Hello/Basic.lean
test_cmd_fails git -C .lake/packages/hello diff --exit-code
test_out "has local changes" build
test_cmd_eq "Hello, changes!" ./.lake/build/bin/test
test_cmd git -C .lake/packages/hello reset --hard
test_no_stderr build

# Test no `git fetch` on a `lake build` if already on the proper revision
# See https://github.com/leanprover/lake/issues/104

echo "# TEST: No fetch"

TEST_URL=https://example.com/hello.git
TEST_MAP="{\"hello\" : \"$TEST_URL\"}"

# build should succeed despite the invalid remote because the
# remote should not be fetched (and nothing should be checked out)
LAKE_PKG_URL_MAP=$TEST_MAP test_not_out "checking" build

# Test that a dependency is materialized as a treeless partial clone
# See https://github.com/leanprover/lean4/issues/10603

echo "# TEST: Partial clone"

rm -rf .lake/packages
test_out "checking out revision '$REV_B'" update --keep-toolchain
test_exp "$(git -C .lake/packages/hello config --get remote.origin.partialclonefilter)" = tree:0
# a blob reachable only from an older revision should not have been fetched
# `--batch-all-objects` lists local objects without lazily fetching any
git -C .lake/packages/hello cat-file --batch-all-objects --batch-check='%(objectname)' 2>/dev/null > .lake/objects.out
test_cmd_fails grep -F "$OLD_BLOB" .lake/objects.out

# Test that Lake does not fetch a revision already present in the repository

echo "# TEST: Local revision"

# check out an older revision, fetching its trees and blobs
sed_i "s/$REV_B/$REV_A/" lake-manifest.json
test_out "checking out revision '$REV_A'" build
# returning to the newer revision needs no fetch, so an invalid remote is harmless
sed_i "s/$REV_A/$REV_B/" lake-manifest.json
LAKE_PKG_URL_MAP=$TEST_MAP test_out "checking out revision '$REV_B'" build

# Test that Lake reuses the repository directory when the URL changes
# See https://github.com/leanprover/lean4/issues/12901

echo "# TEST: URL change"

touch .lake/packages/hello/marker.txt
LAKE_PKG_URL_MAP=$HELLO_MAP test_out "remote URL changed" build
# the repository was reused rather than deleted and cloned again
test_exp -f .lake/packages/hello/marker.txt

# Cleanup
rm -rf hello/.git
rm -f produced.out
