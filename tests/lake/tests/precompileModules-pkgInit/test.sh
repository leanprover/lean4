#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that elaborating `ExternalMod` succeeds.
# Prior to https://github.com/leanprover/lean4/pull/14326,
# we used to load `Downstream` as a plugin rather than a dynlib.
# This would try to initialize `Downstream`,
# and then (transitively through `Downstream.A`) `Upstream.Detached`.
# But the native symbol to initialize `Upstream.Detached` is not in `Upstream:shared`,
# so we would get a crash.
test_run -v lean ExternalMod.lean

# cleanup
rm -f produced.out
