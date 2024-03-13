#!/usr/bin/env bash
set -euo pipefail
LAKE=${LAKE:-../../.lake/build/bin/lake}
$LAKE build
