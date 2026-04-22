#!/usr/bin/env bash
source ../common.sh

# This test covers the behavior of `lake build`
# with no default targets configured.

test_empty_build() {
cfg_file=$1
test_run -f $cfg_file update
test_out_diff <(cat << 'EOF'
warning: no targets specified and no default targets configured
  Note: This will be an error in a future version of Lake.
  Hint: This warning (or error) can be suppressed with '--allow-empty'.
Nothing to build.
EOF
) -f $cfg_file build
test_err_diff <(cat << 'EOF'
warning: no targets specified and no default targets configured
  Note: This will be an error in a future version of Lake.
  Hint: This warning (or error) can be suppressed with '--allow-empty'.
EOF
) -f $cfg_file build --wfail
test_out_diff <(cat << 'EOF'
Nothing to build.
EOF
) -f $cfg_file build --allow-empty --wfail
test_exp ! -f .lake/build/lib/lean/Lib.olean
}

# Test Lean configuration with no default targets
./clean.sh
echo "# TEST: lakefile.lean"
test_empty_build lakefile.lean

# Test TOML configuration with no default targets
./clean.sh
echo "# TEST: lakefile.toml"
test_empty_build lakefile.toml

# Cleanup
rm -f produced.*
