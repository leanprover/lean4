#!/usr/bin/env bash
set -euxo pipefail

# Tests that Lake rebuilds when toolchain changes
# See https://github.com/leanprover/lake/issues/62
# Requires Elan to download a toolchain

# skip if no elan found
if ! command -v elan > /dev/null; then
   echo "elan not found; skipping test"
   exit 0
fi

./clean.sh
elan run --install leanprover/lean4:v4.0.0 lake new foo
cd foo
elan run leanprover/lean4:v4.0.0 lake build +Foo:olean -v | grep --color Foo.olean
rm lean-toolchain
${LAKE:-../../../.lake/build/bin/lake} build -v | grep --color Foo.olean
