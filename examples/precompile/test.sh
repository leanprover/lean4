set -ex

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh
$LAKE -d bar update
$LAKE -d bar build # tests #83
$LAKE -d foo build
