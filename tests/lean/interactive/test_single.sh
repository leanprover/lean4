#!/usr/bin/env bash
if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file] [yes/no]?"
    exit 1
fi
ulimit -s unlimited
LEAN=$1
if command -v greadlink >/dev/null 2>&1; then
  # macOS readlink doesn't support -f option
  READLINK=greadlink
else
  READLINK=readlink
fi
ROOT_PATH=$($READLINK -f ../../..)

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ROOT_PATH_NORMALIZED=$(echo $ROOT_PATH  | sed 's|^/\([a-z]\)/|\U\1:/|' | sed 's|/|\\\\\\\\|g')
else
    ROOT_PATH_NORMALIZED=$ROOT_PATH
fi
export LEAN_PATH=$ROOT_PATH/library:.
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi
f=$2
echo "-- testing $f"

OUTPUT="$("$LEAN" -j0 -D pp.unicode=true --server < "$f")"
# make paths system-independent
if [[ "$OSTYPE" == "msys" ]]; then
    echo "$OUTPUT" | sed "s|$ROOT_PATH_NORMALIZED||g" | sed 's|\\\\|/|g' > "$f.produced.out"
else
    OUTPUT=${OUTPUT//$ROOT_PATH_NORMALIZED/}
    echo "$OUTPUT" > "$f.produced.out"
fi

if test -f "$f.expected.out"; then
    if diff --ignore-all-space "$f.produced.out" "$f.expected.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$f.produced.out" "$f.expected.out"
            if diff --ignore-all-space "$f.produced.out" "$f.expected.out"; then
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
