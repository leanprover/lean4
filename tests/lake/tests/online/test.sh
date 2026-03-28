#!/usr/bin/env bash
source ../common.sh

./clean.sh

export ELAN_TOOLCHAIN=test

./clean.sh
echo "# TEST: Request Errors"
# Tests requiring a package not in the index
test_err "package not found on Reservoir" -f bogus-dep.toml update
# Tests a request error
RESERVOIR_API_URL=example.com \
  test_err "server returned invalid JSON" -f bogus-dep.toml update
RESERVOIR_API_URL=example.com \
  test_err "Reservoir responded with" -f bogus-dep.toml update -v

./clean.sh
echo "# TEST: Non-Reservoir"
test_run -f git.toml update --keep-toolchain
# Test that barrels are not fetched for non-Reservoir dependencies
test_not_out "Cli:optBarrel" -v -f git.toml build @Cli:extraDep

./clean.sh
echo "# TEST: Resveroir"
test_run -f barrel.lean update --keep-toolchain
# Test that a barrel is not fetched for an unbuilt dependency
echo "# TEST: Unbuilt"
test_not_out "Cli:optBarrel" -v -f barrel.lean build @test:extraDep
# Test that barrels are not fetched after the build directory is created.
echo "# TEST: Build directory"
mkdir -p .lake/packages/Cli/.lake/build
test_not_out "Cli:optBarrel" -v -f barrel.lean build @Cli:extraDep
rmdir .lake/packages/Cli/.lake/build
# Test that barrels are not fetched without a toolchain
echo "# TEST: Toolchain"
ELAN_TOOLCHAIN= test_not_out "Cli:optBarrel" -v -f barrel.lean build @Cli:extraDep
test_err "toolchain=test" -v -f barrel.lean build @Cli:barrel
# Test that fetch failures are only shown in verbose mode
echo "# TEST: Verbosity"
test_out "Cli:optBarrel" -v -f barrel.lean build @Cli:extraDep
test_not_out "Cli:optBarrel" -f barrel.lean build @Cli:extraDep
# Test cache toggle
echo "# TEST: Cache toggle"
LAKE_NO_CACHE=1 test_not_out "Cli:optBarrel" -v -f barrel.lean build @Cli:extraDep
test_not_out "Cli:optBarrel" -v -f barrel.lean build @Cli:extraDep --no-cache
LAKE_NO_CACHE=1 test_out "Cli:optBarrel" -v -f barrel.lean build @Cli:extraDep --try-cache
# Test barrel download
echo "# TEST: Download"
ELAN_TOOLCHAIN= \
  test_err "Lean toolchain not known" -v -f barrel.lean build @Cli:barrel
ELAN_TOOLCHAIN=leanprover/lean4:v4.11.0 \
  test_run -v -f barrel.lean build @Cli:barrel
# FIXME: Update
# ELAN_TOOLCHAIN=leanprover/lean4:v4.11.0 \
# LEAN_GITHASH=ec3042d94bd11a42430f9e14d39e26b1f880f99b \
#   test_run -f barrel.lean build Cli --no-build

./clean.sh
echo "# TEST: Resvoir require (Lean)"
test_run -f require.lean update -v --keep-toolchain
test_exp -d .lake/packages/doc-gen4
test_run -f require.lean resolve-deps  # validate manifest

./clean.sh
echo "# TEST: Resvoir require (TOML)"
test_run -f require.toml update -v --keep-toolchain
test_exp -d .lake/packages/doc-gen4
test_run -f require.toml resolve-deps  # validate manifest

# cleanup
rm -f produced.out
