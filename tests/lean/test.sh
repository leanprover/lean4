#!/usr/bin/env bash
cd "$(dirname "$0")"
if [ $# -ne 2 -a $# -ne 1 ]; then
    echo "Usage: test.sh [lean-executable-path] [yes/no]?"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../library:.
if [ $# -ne 2 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$2
fi
NUM_ERRORS=0
for f in *.lean; do
    echo "-- testing $f"
    "$LEAN" -t config.lean "$f" &> "$f.produced.out.1"
    sed "/warning: imported file uses 'sorry'/d" "$f.produced.out.1" > "$f.produced.out"
    rm -f -- "$f.produced.out.1"
    if test -f "$f.expected.out"; then
        if diff -I "executing external script" "$f.produced.out" "$f.expected.out"; then
            echo "-- checked"
        else
            echo "ERROR: file $f.produced.out does not match $f.expected.out"
            NUM_ERRORS=$(($NUM_ERRORS+1))
            if [ $INTERACTIVE == "yes" ]; then
                meld "$f.produced.out" "$f.expected.out"
                if diff -I "executing external script" "$f.produced.out" "$f.expected.out"; then
                    echo "-- mismath was fixed"
                fi
            fi
        fi
    else
        echo "ERROR: file $f.expected.out does not exist"
        NUM_ERRORS=$(($NUM_ERRORS+1))
        if [ $INTERACTIVE == "yes" ]; then
            read -p "copy $f.produced.out (y/n)? "
            if [ $REPLY == "y" ]; then
                cp -- "$f.produced.out" "$f.expected.out"
                echo "-- copied $f.produced.out --> $f.expected.out"
            fi
        fi
    fi
done
if [ $NUM_ERRORS -gt 0 ]; then
    echo "-- Number of errors: $NUM_ERRORS"
    exit 1
else
    echo "-- Passed"
    exit 0
fi
