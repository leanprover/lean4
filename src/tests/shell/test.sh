#!/bin/sh
set -e
if [ $# -ne 1 ]; then
    echo "Usage: test.sh [shell_test-path]"
    exit 1
fi
SHELL_TEST=$1

export LEAN_PATH=../../../library:.
if ! $SHELL_TEST; then
    echo "FAILED"
    exit 1
fi
