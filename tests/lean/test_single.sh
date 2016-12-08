#!/usr/bin/env bash
if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file] [yes/no]?"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../library:.
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi
f=$2
ff=$(./readlinkf.sh "$f")

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
fi

echo "-- testing $f"
"$LEAN" -Dpp.colors=false -Dpp.unicode=true -j0 "$ff" &> "$f.produced.out"
sed "/warning: imported file uses 'sorry'/d" "$f.produced.out" > "$f.produced.out.tmp"
sed "/warning: using 'sorry'/d" "$f.produced.out.tmp" > "$f.produced.out"
sed "/failed to elaborate theorem/d" "$f.produced.out" > "$f.produced.tmp"
sed "s|^$ff|$f|" "$f.produced.tmp" > "$f.produced.out"
if test -f "$f.expected.out"; then
    if diff --ignore-all-space -I "executing external script" "$f.produced.out" "$f.expected.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$f.produced.out" "$f.expected.out"
            if diff -I "executing external script" "$f.produced.out" "$f.expected.out"; then
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
