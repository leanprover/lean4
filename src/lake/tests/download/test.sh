#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

$LAKE update

test -d .lake/packages/Cli
#test -d .lake/packages/std4
test -d .lake/packages/aesop
test -d .lake/packages/doc-gen4

# validate manifest
$LAKE resolve-deps
