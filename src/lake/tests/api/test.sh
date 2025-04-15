#!/usr/bin/env bash
set -euxo pipefail

LEAN=${LEAN:-lean}

# Run Lean tests
$LEAN keys.lean
