#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

$LAKE resolve-deps -R 2>&1 | grep -m2 -E "lorem|ipsum"
$LAKE resolve-deps -R -Kbaz 2>&1 | grep -m3 -E "lorem|ipsum|baz"
$LAKE resolve-deps -R -Kenv=foo 2>&1 | grep -m4 -E "lorem|ipsum|foo|1"
$LAKE resolve-deps -R -Kenv=bar 2>&1 | grep -m4 -E "lorem|ipsum|bar|2"
