#!/bin/bash
if [ $# -ne 2 ]; then
    echo "Usage: test.sh [leanlua-executable-path] [file]"
    exit 1
fi
ulimit -s unlimited
LEANLUA=$1
f=$2
echo "-- testing $f"
if $LEANLUA util.lua $f > $f.produced.out; then
    echo "-- worked"
    exit 0
else
    echo "ERROR executing $f, produced output:"
    cat $f.produced.out
    exit 1
fi
