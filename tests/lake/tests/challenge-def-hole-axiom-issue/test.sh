#!/usr/bin/env bash
source ../common.sh

./clean.sh

init_check_sandbox

# `lake comparator` resolves dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first. Building the project once does the same;
# this just skips the build.
"$LAKE" resolve-deps

test_status_out 1 "Illegal axiom detected: 'sorryAx'" comparator --config config.json

rm -f produced.out
