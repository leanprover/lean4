#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test Lake warnings produce build failures with `--wfail`

$LAKE build warn | grep --color foo
$LAKE build warn --wfail && exit 1 || true

# Test Lean warnings produce build failures with `--wfail`

$LAKE build Warn | grep --color bar
rm .lake/build/lib/Warn.olean # to force a rebuild
$LAKE build Warn --wfail && exit 1 || true
