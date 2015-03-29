#!/usr/bin/env bash
# Script for testing if Lean can parse the output produced by its
# pretty printer
if [ $# -ne 2 ]; then
    echo "Usage: test_single_pp.sh [lean-executable-path] [file]"
    exit 1
fi
ulimit -s 8192
LEAN=$1
f=$2
echo "-- testing $f"
"$LEAN" "$f" showenv.l &> "$f.pp.out"
if grep "===BEGIN ENVIRONMENT===" "$f.pp.out"; then
   awk 'BEGIN { SHOW = 0 } { if (SHOW == 1) print $0 } /===BEGIN ENVIRONMENT===/ { SHOW = 1 }' "$f.pp.out" > "$f.pp"
   rm -f -- "$f.pp.out"
   if "$LEAN" "$f.pp"; then
      rm -f -- "$f.pp"
      echo "-- checked"
   else
      echo "-- failed to parse output produced by Lean"
      exit 1
   fi
else
   echo "-- unexpected output produced by Lean"
   exit 1
fi
