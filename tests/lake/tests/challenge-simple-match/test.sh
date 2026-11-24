#!/usr/bin/env bash
source ../common.sh

./clean.sh

init_check_sandbox

# Without a manifest the command refuses up front, rather than failing inside the sandbox with a
# bare `permission denied` on the manifest it cannot write.
test_status_out 2 'has no `lake-manifest.json`' comparator --config config.json

# `lake comparator` resolves dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first. Building the project once does the same;
# this just skips the build.
"$LAKE" resolve-deps

test_status_out 0 'Your solution is okay!' comparator --config config.json

rm -f produced.out
