#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

TEST_URL=https://example.com/hello.git
MANIFEST=lake-manifest.json

./clean.sh

cd test
$LAKE build
cat $MANIFEST
if [ "`uname`" = Darwin ]; then
  sed -i '' "s,\\.\\.[^\"]*,$TEST_URL," $MANIFEST
else
  sed -i "s,\\.\\.[^\"]*,$TEST_URL," $MANIFEST
fi
cat $MANIFEST
git -C lake-packages/hello remote set-url origin $TEST_URL
$LAKE build -K url=$TEST_URL
