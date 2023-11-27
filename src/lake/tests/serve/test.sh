#!/usr/bin/env bash
set -euo pipefail

if [ "`uname`" = Darwin ]; then
  TAIL=gtail
else
  TAIL=tail
fi

LAKE=${LAKE:-../../.lake/build/bin/lake}

INIT_REQ=$'Content-Length: 46\r\n\r\n{"jsonrpc":"2.0","method":"initialize","id":1}'
INITD_NOT=$'Content-Length: 40\r\n\r\n{"jsonrpc":"2.0","method":"initialized"}'
OPEN_REQ=$'Content-Length: 145\r\n\r\n{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file://Test.lean","languageId":"lean4","version":0,"text":""}}}'
SD_REQ=$'Content-Length: 44\r\n\r\n{"jsonrpc":"2.0","method":"shutdown","id":2}'
EXIT_NOT=$'Content-Length: 33\r\n\r\n{"jsonrpc":"2.0","method":"exit"}'

./clean.sh
echo "does not compile" > lakefile.lean

# ---
# Test that `lake serve` works even if `lakefile.lean` does not compile
# See https://github.com/leanprover/lake/issues/49
# ---

MSGS="$INIT_REQ$INITD_NOT$SD_REQ$EXIT_NOT"
echo -n "$MSGS" | ${LAKE:-../../.lake/build/bin/lake} serve >/dev/null
echo "tested 49"

# ---
# Test that `lake setup-file` retains the error from `lake serve`
# See https://github.com/leanprover/lake/issues/116
# ---

# Test that `lake setup-file` produces the error from `LAKE_INVALID_CONFIG`
set -x
# NOTE: For some reason, using `!` here does not work on macOS
(LAKE_INVALID_CONFIG=$'foo\n' $LAKE setup-file ./Irrelevant.lean 2>&1 && exit 1 || true) | grep foo
set +x

# Test that `lake serve` produces the `Invalid Lake configuration message`.
MSGS="$INIT_REQ$INITD_NOT$OPEN_REQ"
grep -q "Invalid Lake configuration" < <(set +e; (echo -n "$MSGS" && $TAIL --pid=$$ -f /dev/null) | $LAKE serve)
echo "tested 116"
