#!/usr/bin/env bash
if [ $# -eq 0 ]; then
    echo "Usage: run.sh [file] [args]*"
    exit 1
fi
ff=$1
./oldcompile.sh $ff
shift 1
time "./$ff.out" $*
