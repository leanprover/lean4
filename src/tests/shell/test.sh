#!/bin/sh
set -e
if [ $# -ne 1 ]; then
    echo "Usage: test.sh [shell_test-path]"
    exit 1
fi
SHELL_TEST=$1
f="shell_test"

LEAN_PATH=../../../library:. $SHELL_TEST > $f.produced.out

if test -f "$f.expected.out"; then
    if diff --ignore-all-space "$f.produced.out" "$f.expected.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        exit 1
    fi
else
    echo "ERROR: file $f.expected.out does not exist"
    exit 1
fi
