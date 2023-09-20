#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

# Tests that the order in which libraries are declared and required
# is properly preserved and effects which configuration is used for a module.

$LAKE update
$LAKE build +A -v | grep 222000
$LAKE build +A.B -v | grep 333000
$LAKE build +A.B.C -v | grep 333000
$LAKE build +X -v | grep 111000
