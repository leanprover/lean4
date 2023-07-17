#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

$LAKE resolve-deps 2>&1 | grep -m2 -E "lorem|ipsum"
$LAKE resolve-deps -Kbaz 2>&1 | grep -m3 -E "lorem|ipsum|baz"
$LAKE resolve-deps -Kenv=foo 2>&1 | grep -m4 -E "lorem|ipsum|foo|1"
$LAKE resolve-deps -Kenv=bar 2>&1 | grep -m4 -E "lorem|ipsum|bar|2"
