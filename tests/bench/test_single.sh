#!/usr/bin/env bash
if [ $# -ne 2 -a $# -ne 1 ]; then
    echo "Usage: test_single.sh [file] [yes/no]?"
    exit 1
fi
ulimit -s 8192
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$2
fi
ff="$1"

DIFF=diff
if diff --color --help >/dev/null 2>&1; then
  DIFF="diff --color";
fi

./compile.sh "$ff" || exit 1

[ -f "$ff.args" ] && args=$(cat "$ff.args")
"./$ff.out" $args > "$ff.produced.out"
if [ $? -ne 0 ]; then
   echo "Failed to execute $ff.out"
   exit 1
fi

if test -f "$ff.expected.out"; then
    if $DIFF -u --ignore-all-space -I "executing external script" "$ff.expected.out" "$ff.produced.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $ff.produced.out does not match $ff.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$ff.produced.out" "$ff.expected.out"
            if diff -I "executing external script" "$ff.expected.out" "$ff.produced.out"; then
                echo "-- mismatch was fixed"
            fi
        fi
        exit 1
    fi
else
    echo "ERROR: file $ff.expected.out does not exist"
    if [ $INTERACTIVE == "yes" ]; then
        read -p "copy $ff.produced.out (y/n)? "
        if [ $REPLY == "y" ]; then
            cp -- "$ff.produced.out" "$ff.expected.out"
            echo "-- copied $ff.produced.out --> $ff.expected.out"
        fi
    fi
    exit 1
fi
