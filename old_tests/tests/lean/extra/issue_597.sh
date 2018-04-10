#!/bin/bash
set -e
if [ $# -ne 1 ]; then
    echo "Usage: bug_597.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export HLEAN_PATH=../../../hott
"$LEAN" -c 597.clean 597a.hlean
if "$LEAN" -c 597.clean 597b.hlean; then
    echo "ERROR: using incorrect cached value..."
    exit 1
fi
