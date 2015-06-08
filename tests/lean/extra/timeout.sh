#!/bin/sh
# Execute lean with timeout
set -e
if [ $# -ne 3 ]; then
    echo "Usage: timeout.sh [lean-executable-path] [timeout] [benchmark]"
    exit 1
fi
LEAN=$1
TIMEOUT=$2
BENCH=$3
export LEAN_PATH=../../../library:.
ulimit -t $2
if ! $LEAN $BENCH; then
    echo "Failed to execute $BENCH in $TIMEOUT second(s)"
    exit 1
fi
