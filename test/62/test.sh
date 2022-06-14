#!/usr/bin/env bash
set -euxo pipefail

./clean.sh
lake +leanprover/lean4:4.0.0-m3 new foo
cd foo
lake +leanprover/lean4:4.0.0-m3 build | grep -m1 foo
cp ../../../lean-toolchain lean-toolchain
${LAKE:-../../../build/bin/lake} build | grep -m1 foo
