#!/usr/bin/env bash
if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file] [yes/no]?"
    exit 1
fi
ulimit -s 8192
export PATH=$(dirname $(../readlinkf.sh "$1")):$PATH
export LEAN_PATH=../../library:.
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi
f=$2
ff=$(../readlinkf.sh "$f")

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
fi

DIFF=diff
if diff --color --help >/dev/null 2>&1; then
  DIFF="diff --color";
fi

echo "-- testing $f"
bash "$ff" >& "$f.tmp"
echo $? >> "$f.tmp"

sed -E "s|^[^ ]*[/\\\\]||" "$f.tmp" | sed "/WARNING: Lean version mismatch/d" | sed "/^$/d" > "$f.produced.out"
rm "$f.tmp"
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
