#!/usr/bin/env bash
set -exo pipefail

# make prefix `/` behave on MSYS2
[ "$OSTYPE" == "msys" ] && export MSYS2_ARG_CONV_EXCL=*

./clean.sh
LAKE=${LAKE:-../../.lake/build/bin/lake}

$LAKE update
$LAKE script list | tee produced.out
$LAKE run /greet | tee -a produced.out
$LAKE script run greet me | tee -a produced.out
$LAKE script run greet --me | tee -a produced.out
$LAKE script doc greet | tee -a produced.out
$LAKE script run hello | tee -a produced.out
$LAKE script run dep/hello | tee -a produced.out
# Test that non-indentifier names work
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Running.20.60lake.60.20scripts.20from.20the.20command.20line/near/446944450
$LAKE script run say-goodbye | tee -a produced.out
($LAKE script run nonexistent 2>&1 | tee -a produced.out) && exit 1 || true
($LAKE script doc nonexistent 2>&1 | tee -a produced.out) && exit 1 || true
$LAKE scripts | tee -a produced.out
$LAKE run | tee -a produced.out

# FIXME: Figure out why indent in USAGE disappears in the CI
diff --ignore-all-space --strip-trailing-cr expected.out produced.out
