#!/usr/bin/env bash
if [ $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file]"
    exit 1
fi
ulimit -s unlimited
LEAN=$1
f=$2
echo "-- testing $f"
if "$LEAN" extra.lua "$f" > "$f.produced.out"; then
    echo "-- worked"
    exit 0
else
    echo "ERROR executing $f, produced output:"
    cat "$f.produced.out"
    exit 1
fi
