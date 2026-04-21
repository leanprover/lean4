#!/usr/bin/env bash
source ../common.sh

# This test covers the behavoir of `lake build`
# with no default targets configured.

./clean.sh

# Test Lean config
echo "# TEST: lakefile.lean"
test_run -f lakefile.lean update
test_out_diff <(cat << 'EOF'
Build completed successfully (0 jobs).
EOF
) -f lakefile.lean build
test_exp ! -f .lake/build/lib/lean/Lib.olean

./clean.sh

# Test TOML config
echo "# TEST: lakefile.toml"
test_run -f lakefile.toml update
test_out_diff <(cat << 'EOF'
Build completed successfully (0 jobs).
EOF
) -f lakefile.toml build
test_exp ! -f .lake/build/lib/lean/Lib.olean

# Cleanup
rm -f produced.out
