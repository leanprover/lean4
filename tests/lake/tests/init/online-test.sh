#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Ensure that Lake is run without a toolchain name
# (for consistent default behavior in tests)
export ELAN_TOOLCHAIN=

# WARNING: This test of the `math` template will fail unless Mathlib and Lean
# are synchronized.

# Test that Mathlib-standard packages have the expected strict linter options.
mkdir mathlib_standards
pushd mathlib_standards
test_run init mathlib_standards math

# Run via elan to make sure the version of Lean is compatible with the version of Mathlib.

# skip if no elan found
echo "# Check if elan exists"
if ! command -v $ELAN > /dev/null; then
   echo "elan not found; skipping test"
   exit 0
fi

# '#'-commands are not allowed only when enabling the Mathlib standard linters.
echo >MathlibStandards.lean "import Mathlib.Init"
echo >>MathlibStandards.lean "#guard true"
test_cmd_out 'note: this linter can be disabled with `set_option linter.hashCommand false`' $ELAN run $(cat lean-toolchain) lake build mathlib_standards
popd
