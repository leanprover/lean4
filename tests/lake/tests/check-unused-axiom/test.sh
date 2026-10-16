#!/usr/bin/env bash
source ../common.sh

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: lake check needs Linux namespaces"
  exit 0
fi

# User namespaces cannot be assumed available in CI containers; see `../fake-bwrap.sh`.
export COMPARATOR_BWRAP="$PWD/../fake-bwrap.sh"

# `lake check` resolves dependencies inside the sandbox, which cannot write to the project
# directory, so the manifest has to be in place first.
"$LAKE" resolve-deps

test_status_out 0 'Lean default kernel accepts the solution' check

# The half of `lake check` that runs inside the sandbox writes the export to standard out: the
# unused axiom is not in it, while the standard ones are.
mkdir -p work
LAKE_CHECK_EXPORT=1 "$LAKE" check > work/export.ndjson
no_match_text '"str":"unusedAx"' work/export.ndjson
match_text '"str":"propext"' work/export.ndjson

rm -f produced.out
