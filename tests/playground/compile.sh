#!/usr/bin/env bash
if [ $# -eq 0 ]; then
    echo "Usage: compile.sh [file]"
    exit 1
fi
ulimit -s 8192
source ../compiler/test_flags.sh
BIN_DIR=../../bin
LEAN=$BIN_DIR/lean
INCLUDE_DIR=../../src
export LEAN_PATH=../../library:.
ff=$1

# Hack for converting a list of libraries such as `/usr/lib/gmp.so;dl` into valid liker parameters.
LINKER_LIBS=""
for lib in ${LIBS//;/ }; do
  if [[ $lib == *".so" || $lib == *".dll" || $lib == *".dylib" ]]; then
    LINKER_LIBS="$LINKER_LIBS $lib"
  else
    LINKER_LIBS="$LINKER_LIBS -l$lib"
  fi
done

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
fi

$LEAN --cpp="$ff".cpp "$ff"
if [ $? -ne 0 ]; then
    echo "Failed to compile $ff into C++ file"
    exit 1
fi

$CXX -o "$ff.out" -I $INCLUDE_DIR $CXX_FLAGS $ff.cpp $BIN_DIR/libleanstatic.a $LINKER_FLAGS $LINKER_LIBS
if [ $? -ne 0 ]; then
    echo "Failed to compile C++ file $ff.cpp"
    exit 1
fi
