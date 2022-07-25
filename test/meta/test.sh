#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

$LAKE update |& grep -m2 -E "lorem|ipsum"
$LAKE update -Kbaz |& grep -m3 -E "lorem|ipsum|baz"
$LAKE update -Kenv=foo |& grep -m4 -E "lorem|ipsum|foo|1"
$LAKE update -Kenv=bar |& grep -m4 -E "lorem|ipsum|bar|2"
