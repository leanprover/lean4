#!/usr/bin/env bash
if [ $# -ne 1 ]; then
    echo "Usage: test_all.sh [lean-executable-path]"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../../library:.
fs=()
for f in *.lean
do
    ff=$(../readlinkf.sh "$f")
    if [[ "$OSTYPE" == "msys" ]]; then
        # Windows running MSYS2
        # Replace /c/ with c:, and / with \\
        ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
    fi
    fs+=("$ff")
done
"$LEAN" --test-suite "${fs[@]}" || (rm *.test_suite.out *.status; false)
