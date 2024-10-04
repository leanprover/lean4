#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
# Tests requiring a package not in the index
($LAKE update -f bogus-dep.toml 2>&1 && exit || true) |
  grep --color "error: bogus/bogus: could not materialize package: dependency has no explicit source and was not found on Reservoir"

./clean.sh
$LAKE update -f lakefile.lean -v
test -d .lake/packages/doc-gen4
$LAKE resolve-deps -f lakefile.lean # validate manifest

./clean.sh
$LAKE update -f lakefile.toml -v
test -d .lake/packages/doc-gen4
$LAKE resolve-deps -f lakefile.toml # validate manifest
