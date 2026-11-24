#!/usr/bin/env bash
source ../common.sh

./clean.sh

init_check_sandbox

# Without a manifest the command refuses up front, rather than failing inside the sandbox with a
# bare `permission denied` on the manifest it cannot write.
test_status_out 2 'has no `lake-manifest.json`' check

# `lake check` resolves dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first. Building the project once does the same;
# this just skips the build.
"$LAKE" resolve-deps

test_status_out 0 'Lean default kernel accepts the solution' check
match_text 'Uses axioms: propext, Classical.choice, Quot.sound' produced.out

rm -f produced.out
