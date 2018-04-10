#!/usr/bin/env bash
if [ $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file]"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../../library:.
f=$2
echo "-- testing $f"
if [[ -f $f.status ]]; then
    echo "-- using result from test_all.sh"
    cat $f.test_suite.out
    status=$(cat $f.status)
    rm $f.test_suite.out $f.status
else
    "$LEAN" -j 0 "$f"
    status=$?
fi
if [ "$status" -eq 1 ]; then
    echo "-- checked"
else
    echo "failed $f"
    exit 1
fi
