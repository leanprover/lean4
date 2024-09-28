#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
# Test barrel download
$LAKE -f barrel.lean update
ELAN_TOOLCHAIN=leanprover/lean4:v4.12.0-rc1 \
RESERVOIR_API_URL=https://8erdxqo0tltkd0jcjrbywklubs4--reservoir-lean-lang.netlify.app/api/v1 \
  $LAKE -f barrel.lean build @Cli:barrel -v
ELAN_TOOLCHAIN=leanprover/lean4:v4.12.0-rc1 \
LEAN_GITHASH=e9e858a4484905a0bfe97c4f05c3924ead02eed8 \
RESERVOIR_API_URL=https://8erdxqo0tltkd0jcjrbywklubs4--reservoir-lean-lang.netlify.app/api/v1 \
  $LAKE -f barrel.lean build Cli --no-build
exit 0

./clean.sh
# Tests requiring a package not in the index
($LAKE -f bogus-dep.toml update 2>&1 && exit || true) |
  grep --color "error: bogus/bogus: could not materialize package: dependency has no explicit source and was not found on Reservoir"

./clean.sh
$LAKE -f require.lean update -v
test -d .lake/packages/doc-gen4
$LAKE -f require.lean resolve-deps  # validate manifest

./clean.sh
$LAKE -f require.toml update  v
test -d .lake/packages/doc-gen4
$LAKE -f require.toml resolve-deps  # validate manifest
