#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

# Ensure Lake thinks there is a elan environment configured
export ELAN_HOME=

# Tests the toolchain update functionality of `lake update`

RESTART_CODE=4

test_update(){
   ELAN=true $LAKE update 2>&1 | grep --color "updating toolchain to '$1'"
   cat lean-toolchain | diff - <(echo -n "$1")
}

# Test toolchain version API
$LAKE lean test.lean

# Test no toolchain information
./clean.sh
$LAKE update 2>&1 | grep --color "toolchain not updated; no toolchain information found"

# Test a single unknown candidate
./clean.sh
echo lean-a > a/lean-toolchain
test_update lean-a

# Test a single known (PR) candidate
./clean.sh
echo pr-release-101 > a/lean-toolchain
test_update leanprover/lean4-pr-releases:pr-release-101

# Test release comparison
./clean.sh
echo v4.4.0 > a/lean-toolchain
echo v4.8.0 > b/lean-toolchain
test_update leanprover/lean4:v4.8.0

# Test nightly comparison
./clean.sh
echo nightly-2024-10-01 > a/lean-toolchain
echo nightly-2024-01-10 > b/lean-toolchain
test_update leanprover/lean4:nightly-2024-10-01

# Test up-to-date root
./clean.sh
echo v4.4.0 > a/lean-toolchain
echo v4.8.0 > b/lean-toolchain
echo v4.10.0 > lean-toolchain
$LAKE update 2>&1 | grep --color "toolchain not updated; already up-to-date"

# Test multiple candidates
./clean.sh
echo lean-a > a/lean-toolchain
echo lean-b > b/lean-toolchain
$LAKE update 2>&1 | grep --color "toolchain not updated; multiple toolchain candidates"

# Test manual restart
./clean.sh
echo lean-a > a/lean-toolchain
ELAN= $LAKE update 2>&1 && exit 1 || [ $? = $RESTART_CODE ]

# Test elan restart
./clean.sh
echo lean-a > a/lean-toolchain
ELAN=echo $LAKE update | grep --color "run --install lean-a lake update"
