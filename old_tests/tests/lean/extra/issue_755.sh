#!/bin/bash
set -e
if [ $# -ne 1 ]; then
    echo "Usage: issue_755.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export HLEAN_PATH=../../../hott
produced="755.produced.out"
expected="755.expected.out"
$LEAN --line=55 --col=50 --goal 755.hlean &> $produced
if test -f $expected; then
   if diff --ignore-all-space -I "executing external script" "$produced" "$expected"; then
       echo "-- checked"
   else
       echo "ERROR: file $produced does not match $expected"
       exit 1
   fi
else
    echo "ERROR: file $expected does not exist"
    exit 1
fi
echo "done"
