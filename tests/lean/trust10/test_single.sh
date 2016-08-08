#!/usr/bin/env bash
if [ $# -lt 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file] [options]"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../../library:.
f=$2
shift 2
echo "-- testing $f"
if "$LEAN" "$f" $@; then
   echo "-- checked"
else
   echo "failed $f"
   exit 1
fi
