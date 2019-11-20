#!/usr/bin/env bash
if [ $# -ne 2 -a $# -ne 1 ]; then
    echo "Usage: test_single.sh [file] [yes/no]?"
    exit 1
fi
ulimit -s 8192
BIN_DIR=../../bin
export LEAN_PATH=Init=../../library/Init:Test=.
if [ $# -ne 2 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$2
fi
f=$1
ff=$(../lean/readlinkf.sh "$f")

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
fi

DIFF=diff
if diff --color --help >/dev/null 2>&1; then
  DIFF="diff --color";
fi

$BIN_DIR/lean --c="$ff".c "$ff"
if [ $? -ne 0 ]; then
    echo "Failed to compile $ff into C file"
    exit 1
fi

$BIN_DIR/leanc -O3 -DNDEBUG -shared -o "$ff.so" $ff.c
if [ $? -ne 0 ]; then
    echo "Failed to compile C file $ff.c"
    exit 1
fi

$BIN_DIR/lean --plugin="$ff.so" "$ff" 2>&1 | sed "s|^$ff|$f|" > "$f.produced.out"
if test -f "$f.expected.out"; then
    if $DIFF -u --ignore-all-space -I "executing external script" "$f.expected.out" "$f.produced.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$f.produced.out" "$f.expected.out"
            if diff -I "executing external script" "$f.expected.out" "$f.produced.out"; then
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
