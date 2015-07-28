#!/bin/bash
set -e
if [ $# -ne 1 ]; then
    echo "Usage: show_goal_bag.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export LEAN_PATH=../../../library:.

lines=('671' '673'  '677' '661');
cols=('8'  '71' '47' '20');
size=${#lines[@]}

i=0
while [ $i -lt $size ]; do
    line=${lines[$i]}
    col=${cols[$i]}
    let i=i+1
    produced=bag.$line.$col.produced.out
    expected=bag.$line.$col.expected.out
    $LEAN --line=$line --col=$col --goal bag.lean &> $produced
    cp $produced $expected
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
done
echo "done"
