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

# Cleanup
rm -rf hello/.git
rm -f produced.out
