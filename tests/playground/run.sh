#!/usr/bin/env bash
if [ $# -eq 0 ]; then
    echo "Usage: run.sh [file] [args]*"
    exit 1
fi
./compile.sh $1
shift 1
"./$ff.out" $*
