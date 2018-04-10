#!/usr/bin/env bash
if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file] [yes/no]?"
    exit 1
fi
f=$2
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi

DIFF=diff
if diff --color --help >/dev/null 2>&1; then
  DIFF="diff --color";
fi

./run_single.sh $1 $f > "$f.produced.out"

if test -f "$f.expected.out"; then
    if $DIFF -u --ignore-all-space "$f.expected.out" "$f.produced.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$f.produced.out" "$f.expected.out"
            if $DIFF --ignore-all-space "$f.expected.out" "$f.produced.out"; then
                echo "-- mismatch was fixed"
            fi
        fi
        exit 1
    fi
else
    echo "ERROR: file $f.expected.out does not exist"
    if [ $INTERACTIVE == "yes" ]; then
        read -p "copy $f.produced.out (y/n)? "
        if [ $REPLY == "y" ]; then
            cp -- "$f.produced.out" "$f.expected.out"
            echo "-- copied $f.produced.out --> $f.expected.out"
        fi
    fi
    exit 1
fi
