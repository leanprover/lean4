#!/bin/bash
set -e
if [ $# -ne 1 ]; then
    echo "Usage: issue_616.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export HLEAN_PATH=../../../hott
"$LEAN" -o f616a.olean 616a.hlean
"$LEAN" -c 616.clean 616b.hlean
if "$LEAN" -c 616.clean 616c.hlean; then
    echo "ERROR: using incorrect cached value..."
    exit 1
fi
