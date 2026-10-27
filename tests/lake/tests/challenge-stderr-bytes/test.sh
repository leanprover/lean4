#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake comparator needs Linux namespaces"
  exit 0
fi

# User namespaces cannot be assumed available in CI containers; see `../fake-bwrap.sh`.
export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

# `lake comparator` needs the manifest. Without `.lake`, the configuration is elaborated afresh
# inside the sandbox, by the `lake env` whose output `lake comparator` captures, and the byte that
# `lakefile.lean` writes to standard error goes there. Lake passes it on rather than failing to
# decode it.
"$LAKE" resolve-deps
rm -rf .lake

test_status_out 0 'Your solution is okay!' comparator --config config.json
# Matched in a hex dump: whether `grep` finds a byte that is not UTF-8 depends on the `grep` and the
# locale.
od -An -tx1 produced.out > produced.hex
match_text ' ff' produced.hex

rm -f produced.out produced.hex
