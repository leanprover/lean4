#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
$LAKE -f barrel.lean update
# Test cache toggle
$LAKE -f barrel.lean build @Cli:extraDep | grep --color "Cli:optBarrel"
(LAKE_NO_CACHE=1 $LAKE -f barrel.lean build @Cli:extraDep) |
  grep --color "Cli:optBarrel" && exit 1 || true
($LAKE -f barrel.lean build @Cli:extraDep --no-cache) |
  grep --color "Cli:optBarrel" && exit 1 || true
(LAKE_NO_CACHE=1 $LAKE -f barrel.lean build @Cli:extraDep --try-cache) |
  grep --color "Cli:optBarrel"
# Test barrel download
(ELAN_TOOLCHAIN= $LAKE -f barrel.lean build @Cli:barrel -v && exit 1 || true) |
  grep --color "Lean toolchain not known"
ELAN_TOOLCHAIN=leanprover/lean4:v4.9.0 \
  $LAKE -f barrel.lean build @Cli:barrel -v
ELAN_TOOLCHAIN=leanprover/lean4:v4.9.0 \
LEAN_GITHASH=8f9843a4a5fe1b0c2f24c74097f296e2818771ee \
  $LAKE -f barrel.lean build Cli --no-build

./clean.sh
# Tests requiring a package not in the index
($LAKE -f bogus-dep.toml update 2>&1 && exit 1 || true) |
  grep --color "error: bogus/bogus: could not materialize package: dependency has no explicit source and was not found on Reservoir"

./clean.sh
$LAKE -f require.lean update -v
test -d .lake/packages/doc-gen4
$LAKE -f require.lean resolve-deps  # validate manifest

./clean.sh
$LAKE -f require.toml update  v
test -d .lake/packages/doc-gen4
$LAKE -f require.toml resolve-deps  # validate manifest
