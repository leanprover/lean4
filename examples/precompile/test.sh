set -ex

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh
#$LAKE -d bar build # errors: see #83
$LAKE -d foo build
