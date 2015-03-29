#!/bin/bash
# Test is all examples in the .org files are working
if [ $# -ne 2 ]; then
    echo "Usage: test_single.sh [lean-executable-path] [file]"
    exit 1
fi
ulimit -s unlimited
LEAN=$1
export LEAN_PATH=.:../../library
f=$2
i=0
in_code_block=0
lastbegin=0
linenum=0
echo "-- testing $f"
while read -r line; do
    linenum=$((linenum + 1))
    if [[ $line =~ ^#\+BEGIN_SRC\ lean ]]; then
        in_code_block=1
        i=$((i + 1))
        lastbegin=$linenum
        rm -f -- "$f.$i.lean"
    elif [[ $line =~ ^#\+END_SRC ]]; then
        if [[ $in_code_block -eq 1 ]]; then
            if "$LEAN" -t 100000 "$f.$i.lean" > "$f.$i.produced.out"; then
                echo "code fragment #$i worked"
            else
                echo "ERROR executing $f.$i.lean, for in_code_block block starting at $lastbegin, produced output:"
                cat  "$f.$i.produced.out"
                exit 1
            fi
        fi
        in_code_block=0
    elif [[ $in_code_block -eq 1 ]]; then
        echo -E "$line" >> "$f.$i.lean"
    fi
done < "$f"
rm -f "$f.*.produced.out"
rm -f "$f.*.lean"
exit 0
