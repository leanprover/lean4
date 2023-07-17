set -ex

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

$LAKE exe hello
$LAKE exe hello Bob Bill
build/bin/hello
