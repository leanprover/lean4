#!/bin/sh
LEAN=$1         # Lean executable
SOURCE_DIR=$2   # Where the .lean and .lua auxiliary files are located
LEAN_FILE=$3    # Lean file to be exported
DEST=$4         # where to put the CPP file
ARGS=$5         # extra arguments
if $LEAN -q $ARGS $LEAN_FILE $SOURCE_DIR/name_conv.lua $SOURCE_DIR/lean2h.lean > $DEST.tmp
then
    mv $DEST.tmp $DEST
else
    echo "Failed to generate $DEST"
    exit 1
fi
