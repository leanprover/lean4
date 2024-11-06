#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../../.lake/build/bin/lake}

# Tests which require Elan to download a toolchain

# skip if no elan found
if ! command -v elan > /dev/null; then
   echo "elan not found; skipping test"
   exit 0
fi

# Test that Lake rebuilds when toolchain changes
# See https://github.com/leanprover/lake/issues/62

TOOLCHAIN=leanprover/lean4:v4.0.0
./clean.sh
elan run --install $TOOLCHAIN lake new foo
pushd foo
elan run $TOOLCHAIN lake build +Foo:olean -v | grep --color Foo.olean
rm lean-toolchain # switch to Lake under test
$LAKE build -v | grep --color Foo.olean
popd

# Test Lake runs under the new toolchain after Lake updates it
rm -f foo/lake-manifest.json
echo $TOOLCHAIN > foo/lean-toolchain
$LAKE update
grep --color -F '"version": 5' lake-manifest.json
