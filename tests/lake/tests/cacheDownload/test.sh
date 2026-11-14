#!/usr/bin/env bash
source ../common.sh
PYTHON="${PYTHON:-python3}"
if ! "$PYTHON" -c 'import sys; sys.exit(sys.version_info < (3, 11))' 2> /dev/null; then
  echo "SKIPPED: $PYTHON 3.11 or later not found"
  exit 0
fi
"$PYTHON" test.py
