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

# Cleanup
./clean.sh
