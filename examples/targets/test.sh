set -e

LAKE=${LAKE:-../../build/bin/lake}

set -x

if [ "$OS" = Windows_NT ]; then
SHARED_LIB_EXT=dll
elif [ "`uname`" = Darwin ]; then
SHARED_LIB_EXT=dylib
else
SHARED_LIB_EXT=so
fi

./clean.sh

$LAKE build +Foo.Test
$LAKE build Bar:o

$LAKE build

./build/bin/c
test -f ./build/lib/Foo.olean

$LAKE build a b

./build/bin/a
./build/bin/b

$LAKE build foo:static
$LAKE build bar:shared

test -f ./build/lib/libFoo.a
test -f ./build/lib/Bar.$SHARED_LIB_EXT
