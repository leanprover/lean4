#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}
$LAKE script list | tee produced.out
$LAKE run scripts/greet | tee -a produced.out
$LAKE script run greet me | tee -a produced.out
$LAKE script doc greet | tee -a produced.out
($LAKE script run nonexistant 2>&1 | tee -a produced.out) && false || true
($LAKE script doc nonexistant 2>&1 | tee -a produced.out) && false || true
$LAKE scripts | tee -a produced.out
$LAKE run | tee -a produced.out

# TODO: Figure out why indent in USAGE disappears in the CI
diff --ignore-all-space --strip-trailing-cr expected.out produced.out
