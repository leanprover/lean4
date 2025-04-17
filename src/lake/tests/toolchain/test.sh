#!/usr/bin/env bash
source ../common.sh

# Tests which require Elan to download a toolchain

# skip if no elan found
echo "# Check if elan exists"
if ! command -v elan > /dev/null; then
   echo "elan not found; skipping test"
   exit 0
fi

echo "# TESTS"

# Test that Lake rebuilds when toolchain changes
# See https://github.com/leanprover/lake/issues/62

TOOLCHAIN=leanprover/lean4:v4.0.0
./clean.sh
test_cmd elan run --install $TOOLCHAIN lake new foo
pushd foo
test_cmd_out "Foo.olean" elan run $TOOLCHAIN lake build +Foo:olean -v
test_cmd rm lean-toolchain # switch to Lake under test
test_out "Foo.olean" build -v
popd

# Test Lake runs under the new toolchain after Lake updates it
rm -f foo/lake-manifest.json
echo $TOOLCHAIN > foo/lean-toolchain
test_run update
test_cmd grep --color -F '"version": 5' lake-manifest.json
