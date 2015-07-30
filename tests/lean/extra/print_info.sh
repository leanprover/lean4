#!/bin/bash
set -e
if [ $# -ne 1 ]; then
    echo "Usage: print_info.sh [lean-executable-path]"
    exit 1
fi
LEAN=$1
export LEAN_PATH=../../../library:.

lines=('4'  '7'  '8'  '12' '12' '12' '17' '17' '21' '21' '21');
cols=('16'  '18' '19' '19' '20' '30' '0'  '2'  '0'  '1'  '3');
size=${#lines[@]}

i=0
while [ $i -lt $size ]; do
    line=${lines[$i]}
    col=${cols[$i]}
    let i=i+1
    produced=print_info.$line.$col.produced.out
    expected=print_info.$line.$col.expected.out
    $LEAN --line=$line --col=$col --info print_info.lean &> $produced
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
