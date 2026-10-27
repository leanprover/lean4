#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake check needs Linux namespaces"
  exit 0
fi

# Every sandboxed process whose standard error Lake captures writes a byte that is not UTF-8 to it;
# see `bad-stderr-bwrap.sh`. Lake passes it on rather than failing to decode it.
export COMPARATOR_BWRAP="$PWD/bad-stderr-bwrap.sh"

"$LAKE" resolve-deps

test_status_out 0 'Lean default kernel accepts the solution' check
# Matched in a hex dump: whether `grep` finds a byte that is not UTF-8 depends on the `grep` and the
# locale.
od -An -tx1 produced.out > produced.hex
match_text ' ff' produced.hex

rm -f produced.out produced.hex
