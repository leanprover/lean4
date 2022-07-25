#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

$LAKE update 2>&1 | grep -m2 -E "lorem|ipsum"
$LAKE update -Kbaz 2>&1 | grep -m3 -E "lorem|ipsum|baz"
$LAKE update -Kenv=foo 2>&1 | grep -m4 -E "lorem|ipsum|foo|1"
$LAKE update -Kenv=bar 2>&1 | grep -m4 -E "lorem|ipsum|bar|2"
