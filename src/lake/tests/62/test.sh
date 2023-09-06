#!/usr/bin/env bash
set -euxo pipefail

# skip if no elan found
if ! command -v elan > /dev/null; then
   echo "elan not found; skipping test"
   exit 0
fi

if [ "`uname`" = Darwin ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

./clean.sh
elan run leanprover/lean4:nightly-2022-06-30 lake new foo
cd foo
elan run leanprover/lean4:nightly-2022-06-30 lake build +Foo:olean | grep -m1 Foo.olean
rm lean-toolchain
sed_i 's/defaultTarget/default_target/g' lakefile.lean
${LAKE:-../../../build/bin/lake} build -v | grep -m1 Foo.olean
