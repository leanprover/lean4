#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

$LAKE -d app build -v
$LAKE -d lib build -v

$LAKE exe -d app app
$LAKE exe -d lib test

# Tests that a non-precompiled build does not load anything as a dynlib/plugin
# https://github.com/leanprover/lean4/issues/4565
$LAKE -d app build -v | (grep --color -E 'load-dynlib|plugin' && exit 1 || true)
$LAKE -d lib build -v | (grep --color -E 'load-dynlib|plugin' && exit 1 || true)

# Tests the successful precompilation of an `extern_lib`
# Also tests a module with `precompileModules` always precompiles its imports
$LAKE -d app build Test
