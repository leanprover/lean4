#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

$LAKE build warn | grep --color foo
$LAKE build warn --wfail && false || true
