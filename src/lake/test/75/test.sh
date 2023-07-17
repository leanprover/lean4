#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

cd foo
rm -rf build
mkdir -p Foo
echo $'def a := "a"' > Foo/Test.lean
echo $'import Foo.Test def hello := a' > Foo.lean
${LAKE} build
./build/bin/foo | grep -m1 a
echo $'def b := "b"' > Foo/Test.lean
echo $'import Foo.Test def hello := b' > Foo.lean
${LAKE} build Foo
${LAKE} build
./build/bin/foo | grep -m1 b
