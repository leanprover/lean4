#!/usr/bin/env bash
if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file] [yes/no]?"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../library:.
export HLEAN_PATH=../../hott:.
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi
f=$2

if [ ${f: -6} == ".hlean" ]; then
    CONFIG="config.hlean"
else
    CONFIG="config.lean"
fi

echo "-- testing $f"
"$LEAN" $CONFIG "$f" &> "$f.produced.out.1"
sed "/warning: imported file uses 'sorry'/d" "$f.produced.out.1" > "$f.produced.out"
rm -f "$f.produced.out.1"
if test -f "$f.expected.out"; then
    if diff --ignore-all-space -I "executing external script" "$f.produced.out" "$f.expected.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$f.produced.out" "$f.expected.out"
            if diff -I "executing external script" "$f.produced.out" "$f.expected.out"; then
                echo "-- mismath was fixed"
            fi
        else
            diff --ignore-all-space -I "executing external script" "$f.produced.out" "$f.expected.out"
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
