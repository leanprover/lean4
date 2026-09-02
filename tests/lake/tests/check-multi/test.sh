#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake check needs Linux Landlock"
  exit 0
fi

# Landlock cannot be assumed available in CI containers; see `../fake-landrun.sh`.
export COMPARATOR_LANDRUN="$PWD/../fake-landrun.sh"

# `lake check` resolves dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first. Building the project once does the same;
# this just skips the build.
"$LAKE" resolve-deps

# Both roots are built, exported and replayed together, in one sandboxed process: the export
# covers each root's whole import closure, so a pass per root would re-check what they share.
test_status_out 0 'Lean default kernel accepts the solution' check
test_exp "`grep -c 'Building and exporting' produced.out`" = 1
test_exp "`grep -c 'Running Lean default kernel' produced.out`" = 1
match_text 'Built A' produced.out
match_text 'Built B' produced.out

rm -f produced.out
