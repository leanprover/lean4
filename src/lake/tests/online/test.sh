#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
$LAKE update -f lakefile.lean
test -d .lake/packages/doc-gen4
$LAKE resolve-deps -f lakefile.lean # validate manifest


./clean.sh
$LAKE update -f lakefile.toml
test -d .lake/packages/doc-gen4
$LAKE resolve-deps -f lakefile.toml # validate manifest
