#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

export ELAN_TOOLCHAIN=test

./clean.sh
# Tests requiring a package not in the index
($LAKE -f bogus-dep.toml update 2>&1 && exit 1 || true) |
  grep --color "error: bogus/bogus: could not materialize package: dependency has no explicit source and was not found on Reservoir"

./clean.sh
$LAKE -f git.toml update --keep-toolchain
# Test that barrels are not fetched for non-Reservoir dependencies
$LAKE -v -f git.toml build @Cli:extraDep |
  grep --color "Cli:optBarrel" && exit 1 || true

./clean.sh
$LAKE -f barrel.lean update --keep-toolchain
# Test that a barrel is not fetched for an unbuilt dependency
$LAKE -v -f barrel.lean build @test:extraDep |
  grep --color "Cli:optBarrel" && exit 1 || true
# Test that barrels are not fetched after the build directory is created.
mkdir -p .lake/packages/Cli/.lake/build
($LAKE -v -f barrel.lean build @Cli:extraDep) |
  grep --color "Cli:optBarrel" && exit 1 || true
rmdir .lake/packages/Cli/.lake/build
# Test that barrels are not fetched without a toolchain
(ELAN_TOOLCHAIN= $LAKE -v -f barrel.lean build @Cli:extraDep) |
  grep --color "Cli:optBarrel" && exit 1 || true
($LAKE -v -f barrel.lean build @Cli:barrel && exit 1 || true) |
  grep --color "toolchain=test"
# Test that fetch failures are only shown in verbose mode
$LAKE -v -f barrel.lean build @Cli:extraDep |
  grep --color "Cli:optBarrel"
$LAKE -f barrel.lean build @Cli:extraDep |
  grep --color "Cli:optBarrel" && exit 1 || true
# Test cache toggle
(LAKE_NO_CACHE=1 $LAKE -v -f barrel.lean build @Cli:extraDep) |
  grep --color "Cli:optBarrel" && exit 1 || true
($LAKE -v -f barrel.lean build @Cli:extraDep --no-cache) |
  grep --color "Cli:optBarrel" && exit 1 || true
(LAKE_NO_CACHE=1 $LAKE -v -f barrel.lean build @Cli:extraDep --try-cache) |
  grep --color "Cli:optBarrel"
# Test barrel download
(ELAN_TOOLCHAIN= $LAKE -v -f barrel.lean build @Cli:barrel && exit 1 || true) |
  grep --color "Lean toolchain not known"
ELAN_TOOLCHAIN=leanprover/lean4:v4.11.0 \
  $LAKE -v -f barrel.lean build @Cli:barrel
ELAN_TOOLCHAIN=leanprover/lean4:v4.11.0 \
LEAN_GITHASH=ec3042d94bd11a42430f9e14d39e26b1f880f99b \
  $LAKE -f barrel.lean build Cli --no-build

./clean.sh
$LAKE -f require.lean update -v --keep-toolchain
test -d .lake/packages/doc-gen4
$LAKE -f require.lean resolve-deps  # validate manifest

./clean.sh
$LAKE -f require.toml update -v --keep-toolchain
test -d .lake/packages/doc-gen4
$LAKE -f require.toml resolve-deps  # validate manifest
