#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests FFI precompilation across multiple libraries.
# https://github.com/leanprover/lean4/issues/8448

test_run build
test_out_pat '^2$' lean B.lean
test_out_pat '^2$' lean C.lean
test_out_pat '^2$' lean D.lean

# Cleanup
rm -f produced.out
