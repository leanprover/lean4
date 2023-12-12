set -ex

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
$LAKE -d bar update
$LAKE -d bar build # tests #83
$LAKE -d foo build
