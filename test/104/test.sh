#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

TEST_URL=https://example.com/hello.git

./clean.sh

cd test
$LAKE build
cat lean_packages/manifest.json
if [ "`uname`" = Darwin ]; then
  sed -i '' "s,\\.\\.[^\"]*,$TEST_URL," lean_packages/manifest.json
else
  sed -i "s,\\.\\.[^\"]*,$TEST_URL," lean_packages/manifest.json
fi
cat lean_packages/manifest.json
git -C lean_packages/hello remote set-url origin $TEST_URL
$LAKE build -K url=$TEST_URL
