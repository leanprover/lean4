#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test Lake warnings produce build failures with `--wfail`

$LAKE build warn | grep --color foo
$LAKE build warn | grep --color foo # test idempotent
$LAKE build warn --wfail && exit 1 || true

$LAKE build warnArt | grep --color foo-file
$LAKE build warnArt | grep --color foo-file # test `buildFileUpToDate` cache
$LAKE build warnArt --wfail && exit 1 || true

# Test Lean warnings produce build failures with `--wfail`

$LAKE build Warn | grep --color bar
$LAKE build Warn | grep --color bar # test Lean module build log cache
$LAKE build Warn --wfail && exit 1 || true
