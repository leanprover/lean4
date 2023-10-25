#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

$LAKE resolve-deps -R 2>&1
$LAKE resolve-deps -R 2>&1 | grep "impure"
$LAKE resolve-deps -R 2>&1 | (grep -E "foo|bar|baz|1|2" && false || true)
$LAKE resolve-deps -R -Kbaz 2>&1 | grep baz
$LAKE resolve-deps -R -Kenv=foo 2>&1 | grep foo
$LAKE resolve-deps -R -Kenv=bar 2>&1 | grep bar
