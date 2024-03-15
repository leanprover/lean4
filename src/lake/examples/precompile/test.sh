set -ex

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
$LAKE -d bar update
$LAKE -d bar build # tests lake#83
$LAKE -d foo build

./clean.sh
$LAKE -d bar -f lakefile.toml update
$LAKE -d bar -f lakefile.toml build
$LAKE -d foo -f lakefile.toml build
