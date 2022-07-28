#!/usr/bin/env bash
set -euxo pipefail

# skip if no elan found
command -v elan > /dev/null || (echo "elan not found; skipping test"; exit 0)

./clean.sh
lake +leanprover/lean4:nightly-2022-06-30 new foo
cd foo
lake +leanprover/lean4:nightly-2022-06-30 build | grep -m1 foo
cp ../../../lean-toolchain lean-toolchain
${LAKE:-../../../build/bin/lake} build -v | grep -m1 foo
