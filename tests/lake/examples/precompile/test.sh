set -ex

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
$LAKE -d bar update
# test that build a module w/o precompile modules still precompiles deps
# https://github.com/leanprover/lake/issues/83
$LAKE -d bar build
$LAKE -d foo build

./clean.sh
$LAKE -d bar -f lakefile.toml update
$LAKE -d bar -f lakefile.toml build
$LAKE -d foo -f lakefile.toml build
