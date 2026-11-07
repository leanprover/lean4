#!/usr/bin/env bash
source ../common.sh
./clean.sh

# This test covers issue 15435
# https://github.com/leanprover/lean4/issues/15435

# A facet key in `needs` should resolve to the job that every other route to
# that facet uses, however the key spells its package. Each library here needs
# a facet that the same build also requests directly.

# Build the given targets and verify that exactly one job has the caption `$1`.
test_one_job() {
  caption=$1; shift
  lake_out "$@" -v
  test_cmd test "$(grep -c -E -- "\] [A-Za-z]+ $caption( |\$)" produced.out)" = 1
}

for cfg in lakefile.toml lakefile.lean; do
  ./clean.sh
  test_one_job a:exe -f $cfg build a NeedsElided
  ./clean.sh
  test_one_job a:exe -f $cfg build a NeedsNamed
  ./clean.sh
  test_one_job Lib:c.o -f $cfg build +Lib:c.o.noexport NeedsModule
done

# A library's shared library named by key in `plugins` or `moreLinkLibs`
# should be fetched where Lake fetches the key, not in a job continuation, where
# fetches of the key from different jobs could each create a job for it. Each
# target fails unless the key is in the build store (see `checkStored`).
./clean.sh
LEAN_NUM_THREADS=1 test_run -f lakefile.lean build pluginsFetched
./clean.sh
LEAN_NUM_THREADS=1 test_run -f lakefile.lean build linkLibsFetched

# A package's own facet, or a facet of a target whose job has not finished,
# should still be fetched in a job continuation. Each target resolves the
# promise that its module's plugin waits for (in the fetch function of the
# facet `gated`, or in the job of the target `delayed`) only after its fetch
# of the module's `presetup` returns.
./clean.sh
test_run -f lakefile.lean build gatedFetched
./clean.sh
test_run -f lakefile.lean build delayedFetched

# Cleanup
./clean.sh
