#!/usr/bin/env bash

set -e

if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file] [yes/no]?"
    exit 1
fi
ulimit -s 8192
LEAN=$1
BIN_DIR=../../../bin
export LEAN_PATH=Init=../../../src/Init:Test=.

if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi
ff=$2

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
fi

DIFF=diff
if diff --color --help >/dev/null 2>&1; then
  DIFF="diff --color";
fi

$LEAN --cpp="$ff".cpp "$ff" || echo oh ho!
if [ $? -ne 0 ]; then
    echo "Failed to compile $ff into C++ file"
    exit 1
fi

$BIN_DIR/leanc -O3 -DNDEBUG -o "$ff.out" $ff.cpp
if [ $? -ne 0 ]; then
    echo "Failed to compile C++ file $ff.cpp"
    exit 1
fi
"./$ff.out" > "$ff.produced.out" 2>&1 || true

if test -f "$ff.expected.out"; then
    if $DIFF -u --ignore-all-space -I "executing external script" "$ff.expected.out" "$ff.produced.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $ff.produced.out does not match $ff.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$ff.produced.out" "$ff.expected.out"
            if diff -I "executing external script" "$ff.expected.out" "$ff.produced.out"; then
                echo "-- mismatch was fixed"
            fi
        fi
        exit 1
    fi
else
    echo "ERROR: file $ff.expected.out does not exist"
    if [ $INTERACTIVE == "yes" ]; then
        read -p "copy $ff.produced.out (y/n)? "
        if [ $REPLY == "y" ]; then
            cp -- "$ff.produced.out" "$ff.expected.out"
            echo "-- copied $ff.produced.out --> $ff.expected.out"
        fi
    fi
    exit 1
fi
