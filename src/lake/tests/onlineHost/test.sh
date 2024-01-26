#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

export LAKE_RESERVOIR_URL="f508hw7olmqvxd1mcnuuai9ryma--vermillion-stardust-57acd6.netlify.app/api"

$LAKE update -v

test -d .lake/packages/Cli
test -d .lake/packages/std
test -d .lake/packages/doc-gen4

# validate manifest
$LAKE resolve-deps
