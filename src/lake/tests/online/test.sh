#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh
# Tests requiring a package not in the index
($LAKE -f bogus-dep.toml update 2>&1 && exit 1 || true) |
  grep --color "error: bogus/bogus: could not materialize package: dependency has no explicit source and was not found on Reservoir"

./clean.sh
$LAKE -f git.toml update
# Test that barrels are not fetched for non-Reservoir dependencies
$LAKE -v -f git.toml build @Cli:extraDep |
  grep --color "Cli:optBarrel" && exit 1 || true

./clean.sh
$LAKE -f barrel.lean update
# Test that fetch failures are only shown in verbose mode
$LAKE -v -f barrel.lean build @Cli:extraDep |
  grep --color "Cli:optBarrel"
$LAKE -f barrel.lean build @Cli:extraDep |
  grep --color "Cli:optBarrel" && exit 1 || true
$LAKE -f barrel.lean build @Cli:extraDep |
  grep --color "(run with '-v' for details)"
# Test cache toggle
(LAKE_NO_CACHE=1 $LAKE -v -f barrel.lean build @Cli:extraDep) |
  grep --color "Cli:optBarrel" && exit 1 || true
($LAKE -v -f barrel.lean build @Cli:extraDep --no-cache) |
  grep --color "Cli:optBarrel" && exit 1 || true
(LAKE_NO_CACHE=1 $LAKE -v -f barrel.lean build @Cli:extraDep --try-cache) |
  grep --color "Cli:optBarrel"
# Test barrel download
(ELAN_TOOLCHAIN= $LAKE -f barrel.lean build @Cli:barrel -v && exit 1 || true) |
  grep --color "Lean toolchain not known"
ELAN_TOOLCHAIN=leanprover/lean4:v4.11.0 \
  $LAKE -f barrel.lean build @Cli:barrel -v
ELAN_TOOLCHAIN=leanprover/lean4:v4.11.0 \
LEAN_GITHASH=ec3042d94bd11a42430f9e14d39e26b1f880f99b \
  $LAKE -f barrel.lean build Cli --no-build

./clean.sh
$LAKE -f require.lean update -v
test -d .lake/packages/doc-gen4
$LAKE -f require.lean resolve-deps  # validate manifest

./clean.sh
$LAKE -f require.toml update  v
test -d .lake/packages/doc-gen4
$LAKE -f require.toml resolve-deps  # validate manifest
