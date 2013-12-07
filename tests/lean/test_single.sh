#!/bin/bash
if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test.sh [lean-executable-path] [file] [yes/no]?"
    exit 1
fi
ulimit -s 8192
LEAN=$1
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi
f=$2
echo "-- testing $f"
$LEAN config.lean $f > $f.produced.out
if test -f $f.expected.out; then
    if diff $f.produced.out $f.expected.out; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld $f.produced.out $f.expected.out
            if diff $f.produced.out $f.expected.out; then
                echo "-- mismath was fixed"
            fi
        else
            diff $f.produced.out $f.expected.out
        fi
        exit 1
    fi
else
    echo "ERROR: file $f.expected.out does not exist"
    if [ $INTERACTIVE == "yes" ]; then
        read -p "copy $f.produced.out (y/n)? "
        if [ $REPLY == "y" ]; then
            cp $f.produced.out $f.expected.out
            echo "-- copied $f.produced.out --> $f.expected.out"
        fi
    fi
    exit 1
fi
