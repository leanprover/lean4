#!/bin/sh
# Test is all examples in the .md files are working
if [ $# -ne 1 ]; then
    echo "Usage: test.sh [lean-executable-path]"
    exit 1
fi
ulimit -s unlimited
LEAN=$1
NUM_ERRORS=0
for f in `ls *.md`; do
    echo "-- testing $f"
    awk 'BEGIN{ in_block = 0 } !/```/{ if (in_block == 1) print $0; else print "" } /```/ && !/```lean/{ in_block = 0; print "" } /```lean/{ in_block = 1; print "" }' "$f" > "$f.lean"
    if "$LEAN" "$f.lean" > "$f.produced.out"; then
        echo "-- worked"
    else
        echo "ERROR executing $f.lean, produced output is at $f.produced.out"
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
