#!/bin/sh
# Test is all examples in the .md files are working
if [ $# -ne 2 ]; then
    echo "Usage: test.sh [lean-executable-path] [file]"
    exit 1
fi
ulimit -s unlimited
LEAN=$1
f=$2
echo "-- testing $f"
awk 'BEGIN{ in_block = 0 } !/```/{ if (in_block == 1) print $0; else print "" } /```/ && !/```lua/{ in_block = 0; print "" } /```lua/{ in_block = 1; print "" }' "$f" > "$f.lua"
if "$LEAN" "$f.lua" > "$f.produced.out"; then
    echo "-- worked"
    exit 0
else
    echo "ERROR executing $f.lua, produced output:"
    cat  "$f.produced.out"
    exit 1
fi
