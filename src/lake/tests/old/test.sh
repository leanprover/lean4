#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Tests the `--old` option for using outdate oleans
# See https://github.com/leanprover/lake/issues/44

$LAKE new hello
$LAKE -d hello build
sleep 0.5 # for some reason, delay needed for `--old` rebuild consistency
echo 'def hello := "old"' > hello/Hello.lean
$LAKE -d hello build --old | sed 's/\[.*\] //' | tee produced.out
echo 'def hello := "normal"' > hello/Hello.lean
$LAKE -d hello build | sed 's/\[.*\] //' | tee -a produced.out

grep -i main produced.out
grep -i hello produced.out > produced.out.tmp
mv produced.out.tmp produced.out
if [ "$OS" = Windows_NT ]; then
  sed -i 's/.exe//g' produced.out
  diff --strip-trailing-cr expected.out produced.out
else
  diff expected.out produced.out
fi
