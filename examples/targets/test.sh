#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

if [ "$OS" = Windows_NT ]; then
LIB_PREFIX=
SHARED_LIB_EXT=dll
elif [ "`uname`" = Darwin ]; then
LIB_PREFIX=lib
SHARED_LIB_EXT=dylib
else
LIB_PREFIX=lib
SHARED_LIB_EXT=so
fi

./clean.sh

$LAKE build bark | grep -m1 Bark!
$LAKE build targets/bark_bark | grep -m1 Bark!
$LAKE build Foo.Test:print_src | grep -m1 Test.lean
$LAKE build foo:print_name | grep -m1 foo

$LAKE build +Foo.Test

test -f ./build/lib/Foo/Test.olean
test ! -f ./build/lib/Foo/Test.c

$LAKE build Bar:o

test -f ./build/ir/Bar.o

$LAKE build targets/

./build/bin/c
test -f ./build/lib/Foo.olean
test -f ./build/lib/${LIB_PREFIX}Foo.a
cat ./build/meow.txt | grep -m1 Meow!

$LAKE build foo:shared bar

test -f ./build/lib/${LIB_PREFIX}Foo.$SHARED_LIB_EXT
test -f ./build/lib/${LIB_PREFIX}Bar.$SHARED_LIB_EXT

test ! -f ./build/lib/Baz.olean

$LAKE build a b

./build/bin/a
./build/bin/b

$LAKE build bark | grep -m1 Bark!

$LAKE build targets:print_name | grep -m1 targets

$LAKE build targets:deps && exit 1 || true
