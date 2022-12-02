#!/usr/bin/env bash
set -eu

LAKE=${LAKE:-../../build/bin/lake}

# Test environmnt variable

LAKE_INVALID_CONFIG=$'foo\n' $LAKE print-paths 2>&1 | grep -m1 foo

# Test watchdog

INIT_REQ=$'Content-Length: 46\r\n\r\n{"jsonrpc":"2.0","method":"initialize","id":1}'
INITD_NOT=$'Content-Length: 40\r\n\r\n{"jsonrpc":"2.0","method":"initialized"}'
OPEN_REQ=$'Content-Length: 145\r\n\r\n{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file://Test.lean","languageId":"lean4","version":0,"text":""}}}'
MSGS="$INIT_REQ$INITD_NOT$OPEN_REQ"

set -o pipefail

cp /dev/null lake.in
tail -f lake.in | $LAKE serve 2>&1 > lake.out &
pid=$!
echo -n "$MSGS" >> lake.in
sleep 3
kill $pid

echo
grep -m1 Lake lake.out
