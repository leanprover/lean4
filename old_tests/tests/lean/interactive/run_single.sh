#!/usr/bin/env bash
if [ $# -ne 2 ]; then
    echo "Usage: run_single.sh [lean-executable-path] [file]"
    exit 1
fi
ulimit -s 8192
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
f=$2
if [[ "$f" == *.lean ]]; then
    INPUT="$(./mk_input.sh "$f")"
else
    INPUT="$(cat "$f")"
fi
OUTPUT="$(echo "$INPUT" | "$LEAN" -j0 -D pp.unicode=true --server 2>&1)"
# make paths system-independent
echo "$OUTPUT" | grep -v '"response":"current_tasks"' | sed "s|$ROOT_PATH_NORMALIZED||g" | sed 's|\\\\|/|g' | sed 's/\("source":\){[^}]*}/\1/'
