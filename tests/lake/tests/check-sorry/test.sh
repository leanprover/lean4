#!/usr/bin/env bash
source ../common.sh

./clean.sh

init_check_sandbox

# `lake check` resolves dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first. Building the project once does the same;
# this just skips the build.
"$LAKE" resolve-deps

# The kernel accepts `sorryAx`, so only the axiom report catches this.
test_status_out 1 "Axiom 'sorryAx' is not permitted" check
match_text "it is used by 'bad'" produced.out

# The axiom report comes before any checker runs, so it is not masked by a checker rejecting the
# axiom less clearly (or, here, by the bundled checkers being absent from a development toolchain).
test_status_out 1 "Axiom 'sorryAx' is not permitted" check --paranoid
no_match_text 'kernel' produced.out

rm -f produced.out
