#!/usr/bin/env bash
cd "$(dirname "$0")"
if [ $# -ne 1 ]; then
    echo "Usage: test.sh [lean-executable-path]"
    exit 1
fi
ulimit -s unlimited
LEAN=$1
NUM_ERRORS=0
for f in *.lua; do
    echo "-- testing $f"
    if "$LEAN" "extra.lua" "$f" > "$f.produced.out"; then
        echo "-- worked"
    else
        echo "ERROR executing $f, produced output is at $f.produced.out"
         NUM_ERRORS=$(($NUM_ERRORS+1))
    fi
done
if [ $NUM_ERRORS -gt 0 ]; then
    echo "-- Number of errors: $NUM_ERRORS"
    exit 1
else
    echo "-- Passed"
    exit 0
fi
