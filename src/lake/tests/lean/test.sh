#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

$LAKE lean Test.lean -v | grep --color "Hello from the library foo!"
$LAKE lean Test.lean -- --run Test.lean Bob | grep --color "Hello Bob!"
test -f .lake/build/lib/lean/Lib.olean
