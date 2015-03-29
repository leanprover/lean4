#!/bin/sh
# Regression test for issue https://github.com/leanprover/lean/issues/422
set -e
if [ $# -ne 1 ]; then
    echo "Usage: ac_bug.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export LEAN_PATH=../../../library:.
for f in `ls ac_bug*.input`; do
    echo "testing $f..."
    "$LEAN" --server-trace "$f" > "$f.produced.out"
    if grep "nat.mul.assoc" "$f.produced.out"; then
        echo "FAILED"
        exit 1
    fi
    rm -f -- "$f.produced.out"
done
echo "done"
