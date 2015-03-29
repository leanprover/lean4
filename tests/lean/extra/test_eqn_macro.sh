#!/bin/bash
set -e
if [ $# -ne 1 ]; then
    echo "Usage: test_eq_macro.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export LEAN_PATH=../../../library:.
"$LEAN" -o eqn_macro1.olean eqn_macro1.lean
"$LEAN" eqn_macro2.lean
