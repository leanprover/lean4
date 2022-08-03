#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

$LAKE new hello
$LAKE -d hello build
sleep 0.1 # for some reason, delay needed for `--old` rebuild consistency
echo 'def hello := "old"' > hello/Hello.lean
$LAKE -d hello build --old | tee produced.out
echo 'def hello := "normal"' > hello/Hello.lean
$LAKE -d hello build | tee -a produced.out
if [ "`uname`" = Darwin ]; then
  sed -i '' 's/.exe//g' produced.out
else
  sed -i 's/.exe//g' produced.out
fi
diff expected.out produced.out
