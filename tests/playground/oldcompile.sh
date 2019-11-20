#!/usr/bin/env bash
if [ $# -eq 0 ]; then
    echo "Usage: compile.sh [file]"
    exit 1
fi
ulimit -s 8192
BIN_DIR=../../bin
LEAN=$BIN_DIR/lean
export LEAN_PATH=Init=../../library/Init:Test=.
ff=$1

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
fi

$LEAN --oldcpp="$ff".cpp "$ff"
if [ $? -ne 0 ]; then
    echo "Failed to compile $ff into C++ file"
    exit 1
fi

$BIN_DIR/leanc -O3 -o "$ff.out" $ff.cpp
if [ $? -ne 0 ]; then
    echo "Failed to compile C++ file $ff.cpp"
    exit 1
fi
