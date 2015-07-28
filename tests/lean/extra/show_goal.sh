#!/bin/bash
set -e
if [ $# -ne 1 ]; then
    echo "Usage: show_goal.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export LEAN_PATH=../../../library:.

lines=('6' '6'  '8' '8' '9' '9'  '14' '15' '18' '18' '18' '20' '23' '24' '24');
cols=('0'  '14' '4' '5' '4' '12' '6'  '6'  '20' '21' '6'  '4'  '6'  '2'  '3');
size=${#lines[@]}

i=0
while [ $i -lt $size ]; do
    line=${lines[$i]}
    col=${cols[$i]}
    let i=i+1
    produced=show_goal.$line.$col.produced.out
    expected=show_goal.$line.$col.expected.out
    $LEAN --line=$line --col=$col --goal show_goal.lean &> $produced
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
