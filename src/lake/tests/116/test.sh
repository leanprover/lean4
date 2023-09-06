#!/usr/bin/env bash
set -exuo pipefail

LAKE=${LAKE:-../../build/bin/lake}

if [ "`uname`" = Darwin ]; then
  TAIL=gtail
else
  TAIL=tail
fi

# Test environmnt variable

(LAKE_INVALID_CONFIG=$'foo\n' $LAKE print-paths 2>&1 || true) |  grep -m1 foo

# Test watchdog

set +x

INIT_REQ=$'Content-Length: 46\r\n\r\n{"jsonrpc":"2.0","method":"initialize","id":1}'
INITD_NOT=$'Content-Length: 40\r\n\r\n{"jsonrpc":"2.0","method":"initialized"}'
OPEN_REQ=$'Content-Length: 145\r\n\r\n{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file://Test.lean","languageId":"lean4","version":0,"text":""}}}'
MSGS="$INIT_REQ$INITD_NOT$OPEN_REQ"

grep -q "Invalid Lake configuration" < <(set +e; (echo -n "$MSGS" && $TAIL --pid=$$ -f /dev/null) | $LAKE serve)
echo "done"
