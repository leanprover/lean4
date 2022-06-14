#!/usr/bin/env bash
set -euo pipefail

INIT_REQ=$'Content-Length: 46\r\n\r\n{"jsonrpc":"2.0","method":"initialize","id":1}'
INITD_NOT=$'Content-Length: 40\r\n\r\n{"jsonrpc":"2.0","method":"initialized"}'
SD_REQ=$'Content-Length: 44\r\n\r\n{"jsonrpc":"2.0","method":"shutdown","id":2}'
EXIT_NOT=$'Content-Length: 33\r\n\r\n{"jsonrpc":"2.0","method":"exit"}'
MSGS="$INIT_REQ$INITD_NOT$SD_REQ$EXIT_NOT"

echo "does not compile" > lakefile.lean
echo -n "$MSGS" | ${LAKE:-../../build/bin/lake} serve >/dev/null
rm lakefile.lean
